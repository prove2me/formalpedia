-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0043__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0043__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:13:15.596986+00:00
-- url     : https://prove2.me/theorems/27ead266-18e0-4c32-a3cc-46b6389ed2a0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0043 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0044, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0043 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0044, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0045)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0043 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0044, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0045)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0043 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0044, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0045) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0043 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0044, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0045).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0043 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2752_neg : (7295817 / 1000000000) ≤ -Real.log (2481826831 / 2500000000) ∧
    -Real.log (2481826831 / 2500000000) ≤ (3647909 / 500000000) := by
  have h := checkLog_sound (w := (18173169 / 4981826831)) (n := 12)
    (lo := (7295817 / 1000000000)) (hi := (3647909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2481826831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2481826831) = 1/(2481826831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2752 : Bounds (-3647909 / 500000000) (-7295817 / 1000000000) (Real.log (2481826831 / 2500000000)) := by
  have h := reflection_log_2752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2753_neg : (42733749 / 250000000) ≤ -Real.log (7812500000 / 9268856451) ∧
    -Real.log (7812500000 / 9268856451) ≤ (170934997 / 1000000000) := by
  have h := checkLog_sound (w := (1456356451 / 17081356451)) (n := 12)
    (lo := (42733749 / 250000000)) (hi := (170934997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9268856451 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9268856451 / 7812500000) = 1/(7812500000 / 9268856451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2753 : Bounds (42733749 / 250000000) (170934997 / 1000000000) (Real.log (9268856451 / 7812500000)) := by
  have h := reflection_log_2753_neg
  have he : Real.log (9268856451 / 7812500000) = -Real.log (7812500000 / 9268856451) := by
    rw [show ((9268856451 / 7812500000) : ℝ) = ((7812500000 / 9268856451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2754_neg : (171380241 / 1000000000) ≤ -Real.log (250000000000 / 296735497021) ∧
    -Real.log (250000000000 / 296735497021) ≤ (85690121 / 500000000) := by
  have h := checkLog_sound (w := (46735497021 / 546735497021)) (n := 12)
    (lo := (171380241 / 1000000000)) (hi := (85690121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296735497021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296735497021 / 250000000000) = 1/(250000000000 / 296735497021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2754 : Bounds (171380241 / 1000000000) (85690121 / 500000000) (Real.log (296735497021 / 250000000000)) := by
  have h := reflection_log_2754_neg
  have he : Real.log (296735497021 / 250000000000) = -Real.log (250000000000 / 296735497021) := by
    rw [show ((296735497021 / 250000000000) : ℝ) = ((250000000000 / 296735497021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2755_neg : (342921437 / 1000000000) ≤ -Real.log (500000000000 / 704529029149) ∧
    -Real.log (500000000000 / 704529029149) ≤ (171460719 / 500000000) := by
  have h := checkLog_sound (w := (204529029149 / 1204529029149)) (n := 12)
    (lo := (342921437 / 1000000000)) (hi := (171460719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704529029149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704529029149 / 500000000000) = 1/(500000000000 / 704529029149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2755 : Bounds (342921437 / 1000000000) (171460719 / 500000000) (Real.log (704529029149 / 500000000000)) := by
  have h := reflection_log_2755_neg
  have he : Real.log (704529029149 / 500000000000) = -Real.log (500000000000 / 704529029149) := by
    rw [show ((704529029149 / 500000000000) : ℝ) = ((500000000000 / 704529029149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2756_neg : (171563689 / 500000000) ≤ -Real.log (500000000000 / 704674135647) ∧
    -Real.log (500000000000 / 704674135647) ≤ (343127379 / 1000000000) := by
  have h := checkLog_sound (w := (204674135647 / 1204674135647)) (n := 12)
    (lo := (171563689 / 500000000)) (hi := (343127379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704674135647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704674135647 / 500000000000) = 1/(500000000000 / 704674135647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2756 : Bounds (171563689 / 500000000) (343127379 / 1000000000) (Real.log (704674135647 / 500000000000)) := by
  have h := reflection_log_2756_neg
  have he : Real.log (704674135647 / 500000000000) = -Real.log (500000000000 / 704674135647) := by
    rw [show ((704674135647 / 500000000000) : ℝ) = ((500000000000 / 704674135647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2757_neg : (39250937 / 250000000) ≤ -Real.log (100 / 117) ∧
    -Real.log (100 / 117) ≤ (157003749 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 217)) (n := 12)
    (lo := (39250937 / 250000000)) (hi := (157003749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 100) = 1/(100 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2757 : Bounds (39250937 / 250000000) (157003749 / 1000000000) (Real.log (117 / 100)) := by
  have h := reflection_log_2757_neg
  have he : Real.log (117 / 100) = -Real.log (100 / 117) := by
    rw [show ((117 / 100) : ℝ) = ((100 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2758_neg : (93164789 / 500000000) ≤ -Real.log (83 / 100) ∧
    -Real.log (83 / 100) ≤ (186329579 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 83) = 1/(83 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2758 : Bounds (-186329579 / 1000000000) (-93164789 / 500000000) (Real.log (83 / 100)) := by
  have h := reflection_log_2758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2759_neg : (33997 / 200000000) ≤ -Real.log (100000 / 100017) ∧
    -Real.log (100000 / 100017) ≤ (84993 / 500000000) := by
  have h := checkLog_sound (w := (17 / 200017)) (n := 12)
    (lo := (33997 / 200000000)) (hi := (84993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100017 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100017 / 100000) = 1/(100000 / 100017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2759 : Bounds (33997 / 200000000) (84993 / 500000000) (Real.log (100017 / 100000)) := by
  have h := reflection_log_2759_neg
  have he : Real.log (100017 / 100000) = -Real.log (100000 / 100017) := by
    rw [show ((100017 / 100000) : ℝ) = ((100000 / 100017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2760_neg : (85007 / 500000000) ≤ -Real.log (99983 / 100000) ∧
    -Real.log (99983 / 100000) ≤ (34003 / 200000000) := by
  have h := checkLog_sound (w := (17 / 199983)) (n := 12)
    (lo := (85007 / 500000000)) (hi := (34003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99983) = 1/(99983 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2760 : Bounds (-34003 / 200000000) (-85007 / 500000000) (Real.log (99983 / 100000)) := by
  have h := reflection_log_2760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2761_neg : (81866581 / 1000000000) ≤ -Real.log (1000000 / 1085311) ∧
    -Real.log (1000000 / 1085311) ≤ (40933291 / 500000000) := by
  have h := checkLog_sound (w := (85311 / 2085311)) (n := 12)
    (lo := (81866581 / 1000000000)) (hi := (40933291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085311 / 1000000) = 1/(1000000 / 1085311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2761 : Bounds (81866581 / 1000000000) (40933291 / 500000000) (Real.log (1085311 / 1000000)) := by
  have h := reflection_log_2761_neg
  have he : Real.log (1085311 / 1000000) = -Real.log (1000000 / 1085311) := by
    rw [show ((1085311 / 1000000) : ℝ) = ((1000000 / 1085311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2762_neg : (44585581 / 500000000) ≤ -Real.log (914689 / 1000000) ∧
    -Real.log (914689 / 1000000) ≤ (89171163 / 1000000000) := by
  have h := checkLog_sound (w := (85311 / 1914689)) (n := 12)
    (lo := (44585581 / 500000000)) (hi := (89171163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914689) = 1/(914689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2762 : Bounds (-89171163 / 1000000000) (-44585581 / 500000000) (Real.log (914689 / 1000000)) := by
  have h := reflection_log_2762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2763_neg : (82070189 / 1000000000) ≤ -Real.log (250000 / 271383) ∧
    -Real.log (250000 / 271383) ≤ (8207019 / 100000000) := by
  have h := checkLog_sound (w := (21383 / 521383)) (n := 12)
    (lo := (82070189 / 1000000000)) (hi := (8207019 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271383 / 250000) = 1/(250000 / 271383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2763 : Bounds (82070189 / 1000000000) (8207019 / 100000000) (Real.log (271383 / 250000)) := by
  have h := reflection_log_2763_neg
  have he : Real.log (271383 / 250000) = -Real.log (250000 / 271383) := by
    rw [show ((271383 / 250000) : ℝ) = ((250000 / 271383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2764_neg : (89412803 / 1000000000) ≤ -Real.log (228617 / 250000) ∧
    -Real.log (228617 / 250000) ≤ (22353201 / 250000000) := by
  have h := checkLog_sound (w := (21383 / 478617)) (n := 12)
    (lo := (89412803 / 1000000000)) (hi := (22353201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228617) = 1/(228617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2764 : Bounds (-22353201 / 250000000) (-89412803 / 1000000000) (Real.log (228617 / 250000)) := by
  have h := reflection_log_2764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2765_neg : (3671307 / 500000000) ≤ -Real.log (62042767311 / 62500000000) ∧
    -Real.log (62042767311 / 62500000000) ≤ (1468523 / 200000000) := by
  have h := checkLog_sound (w := (457232689 / 124542767311)) (n := 12)
    (lo := (3671307 / 500000000)) (hi := (1468523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62042767311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62042767311) = 1/(62042767311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2765 : Bounds (-1468523 / 200000000) (-3671307 / 500000000) (Real.log (62042767311 / 62500000000)) := by
  have h := reflection_log_2765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2766_neg : (365229 / 50000000) ≤ -Real.log (992722033279 / 1000000000000) ∧
    -Real.log (992722033279 / 1000000000000) ≤ (7304581 / 1000000000) := by
  have h := checkLog_sound (w := (7277966721 / 1992722033279)) (n := 12)
    (lo := (365229 / 50000000)) (hi := (7304581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992722033279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992722033279) = 1/(992722033279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2766 : Bounds (-7304581 / 1000000000) (-365229 / 50000000) (Real.log (992722033279 / 1000000000000)) := by
  have h := reflection_log_2766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2767_neg : (10689859 / 62500000) ≤ -Real.log (500000000000 / 593267766421) ∧
    -Real.log (500000000000 / 593267766421) ≤ (34207549 / 200000000) := by
  have h := checkLog_sound (w := (93267766421 / 1093267766421)) (n := 12)
    (lo := (10689859 / 62500000)) (hi := (34207549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593267766421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593267766421 / 500000000000) = 1/(500000000000 / 593267766421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2767 : Bounds (10689859 / 62500000) (34207549 / 200000000) (Real.log (593267766421 / 500000000000)) := by
  have h := reflection_log_2767_neg
  have he : Real.log (593267766421 / 500000000000) = -Real.log (500000000000 / 593267766421) := by
    rw [show ((593267766421 / 500000000000) : ℝ) = ((500000000000 / 593267766421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2768_neg : (10717687 / 62500000) ≤ -Real.log (500000000000 / 593531977063) ∧
    -Real.log (500000000000 / 593531977063) ≤ (171482993 / 1000000000) := by
  have h := checkLog_sound (w := (93531977063 / 1093531977063)) (n := 12)
    (lo := (10717687 / 62500000)) (hi := (171482993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593531977063 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593531977063 / 500000000000) = 1/(500000000000 / 593531977063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2768 : Bounds (10717687 / 62500000) (171482993 / 1000000000) (Real.log (593531977063 / 500000000000)) := by
  have h := reflection_log_2768_neg
  have he : Real.log (593531977063 / 500000000000) = -Real.log (500000000000 / 593531977063) := by
    rw [show ((593531977063 / 500000000000) : ℝ) = ((500000000000 / 593531977063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2769_neg : (171563689 / 500000000) ≤ -Real.log (250000000000 / 352337067823) ∧
    -Real.log (250000000000 / 352337067823) ≤ (343127379 / 1000000000) := by
  have h := checkLog_sound (w := (102337067823 / 602337067823)) (n := 12)
    (lo := (171563689 / 500000000)) (hi := (343127379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352337067823 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352337067823 / 250000000000) = 1/(250000000000 / 352337067823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2769 : Bounds (171563689 / 500000000) (343127379 / 1000000000) (Real.log (352337067823 / 250000000000)) := by
  have h := reflection_log_2769_neg
  have he : Real.log (352337067823 / 250000000000) = -Real.log (250000000000 / 352337067823) := by
    rw [show ((352337067823 / 250000000000) : ℝ) = ((250000000000 / 352337067823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2770_neg : (343333327 / 1000000000) ≤ -Real.log (500000000000 / 704819277109) ∧
    -Real.log (500000000000 / 704819277109) ≤ (21458333 / 62500000) := by
  have h := checkLog_sound (w := (204819277109 / 1204819277109)) (n := 12)
    (lo := (343333327 / 1000000000)) (hi := (21458333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704819277109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704819277109 / 500000000000) = 1/(500000000000 / 704819277109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2770 : Bounds (343333327 / 1000000000) (21458333 / 62500000) (Real.log (704819277109 / 500000000000)) := by
  have h := reflection_log_2770_neg
  have he : Real.log (704819277109 / 500000000000) = -Real.log (500000000000 / 704819277109) := by
    rw [show ((704819277109 / 500000000000) : ℝ) = ((500000000000 / 704819277109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2771_neg : (31417843 / 200000000) ≤ -Real.log (10000 / 11701) ∧
    -Real.log (10000 / 11701) ≤ (2454519 / 15625000) := by
  have h := checkLog_sound (w := (1701 / 21701)) (n := 12)
    (lo := (31417843 / 200000000)) (hi := (2454519 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11701 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11701 / 10000) = 1/(10000 / 11701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2771 : Bounds (31417843 / 200000000) (2454519 / 15625000) (Real.log (11701 / 10000)) := by
  have h := reflection_log_2771_neg
  have he : Real.log (11701 / 10000) = -Real.log (10000 / 11701) := by
    rw [show ((11701 / 10000) : ℝ) = ((10000 / 11701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2772_neg : (186450067 / 1000000000) ≤ -Real.log (8299 / 10000) ∧
    -Real.log (8299 / 10000) ≤ (46612517 / 250000000) := by
  have h := checkLog_sound (w := (1701 / 18299)) (n := 12)
    (lo := (186450067 / 1000000000)) (hi := (46612517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8299) = 1/(8299 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2772 : Bounds (-46612517 / 250000000) (-186450067 / 1000000000) (Real.log (8299 / 10000)) := by
  have h := reflection_log_2772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2773_neg : (34017 / 200000000) ≤ -Real.log (10000000 / 10001701) ∧
    -Real.log (10000000 / 10001701) ≤ (85043 / 500000000) := by
  have h := checkLog_sound (w := (1701 / 20001701)) (n := 12)
    (lo := (34017 / 200000000)) (hi := (85043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001701 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001701 / 10000000) = 1/(10000000 / 10001701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2773 : Bounds (34017 / 200000000) (85043 / 500000000) (Real.log (10001701 / 10000000)) := by
  have h := reflection_log_2773_neg
  have he : Real.log (10001701 / 10000000) = -Real.log (10000000 / 10001701) := by
    rw [show ((10001701 / 10000000) : ℝ) = ((10000000 / 10001701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2774_neg : (85057 / 500000000) ≤ -Real.log (9998299 / 10000000) ∧
    -Real.log (9998299 / 10000000) ≤ (34023 / 200000000) := by
  have h := checkLog_sound (w := (1701 / 19998299)) (n := 12)
    (lo := (85057 / 500000000)) (hi := (34023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998299) = 1/(9998299 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2774 : Bounds (-34023 / 200000000) (-85057 / 500000000) (Real.log (9998299 / 10000000)) := by
  have h := reflection_log_2774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2775_neg : (81913571 / 1000000000) ≤ -Real.log (500000 / 542681) ∧
    -Real.log (500000 / 542681) ≤ (20478393 / 250000000) := by
  have h := checkLog_sound (w := (42681 / 1042681)) (n := 12)
    (lo := (81913571 / 1000000000)) (hi := (20478393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542681 / 500000) = 1/(500000 / 542681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2775 : Bounds (81913571 / 1000000000) (20478393 / 250000000) (Real.log (542681 / 500000)) := by
  have h := reflection_log_2775_neg
  have he : Real.log (542681 / 500000) = -Real.log (500000 / 542681) := by
    rw [show ((542681 / 500000) : ℝ) = ((500000 / 542681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2776_neg : (2230673 / 25000000) ≤ -Real.log (457319 / 500000) ∧
    -Real.log (457319 / 500000) ≤ (89226921 / 1000000000) := by
  have h := checkLog_sound (w := (42681 / 957319)) (n := 12)
    (lo := (2230673 / 25000000)) (hi := (89226921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457319) = 1/(457319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2776 : Bounds (-89226921 / 1000000000) (-2230673 / 25000000) (Real.log (457319 / 500000)) := by
  have h := reflection_log_2776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2777_neg : (82117169 / 1000000000) ≤ -Real.log (1000000 / 1085583) ∧
    -Real.log (1000000 / 1085583) ≤ (8211717 / 100000000) := by
  have h := checkLog_sound (w := (85583 / 2085583)) (n := 12)
    (lo := (82117169 / 1000000000)) (hi := (8211717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085583 / 1000000) = 1/(1000000 / 1085583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2777 : Bounds (82117169 / 1000000000) (8211717 / 100000000) (Real.log (1085583 / 1000000)) := by
  have h := reflection_log_2777_neg
  have he : Real.log (1085583 / 1000000) = -Real.log (1000000 / 1085583) := by
    rw [show ((1085583 / 1000000) : ℝ) = ((1000000 / 1085583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2778_neg : (3578743 / 40000000) ≤ -Real.log (914417 / 1000000) ∧
    -Real.log (914417 / 1000000) ≤ (2795893 / 31250000) := by
  have h := checkLog_sound (w := (85583 / 1914417)) (n := 12)
    (lo := (3578743 / 40000000)) (hi := (2795893 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914417) = 1/(914417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2778 : Bounds (-2795893 / 31250000) (-3578743 / 40000000) (Real.log (914417 / 1000000)) := by
  have h := reflection_log_2778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2779_neg : (1470281 / 200000000) ≤ -Real.log (992675550111 / 1000000000000) ∧
    -Real.log (992675550111 / 1000000000000) ≤ (3675703 / 500000000) := by
  have h := checkLog_sound (w := (7324449889 / 1992675550111)) (n := 12)
    (lo := (1470281 / 200000000)) (hi := (3675703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992675550111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992675550111) = 1/(992675550111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2779 : Bounds (-3675703 / 500000000) (-1470281 / 200000000) (Real.log (992675550111 / 1000000000000)) := by
  have h := reflection_log_2779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2780_neg : (1828337 / 250000000) ≤ -Real.log (248178332239 / 250000000000) ∧
    -Real.log (248178332239 / 250000000000) ≤ (7313349 / 1000000000) := by
  have h := checkLog_sound (w := (1821667761 / 498178332239)) (n := 12)
    (lo := (1828337 / 250000000)) (hi := (7313349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248178332239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248178332239) = 1/(248178332239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2780 : Bounds (-7313349 / 1000000000) (-1828337 / 250000000) (Real.log (248178332239 / 250000000000)) := by
  have h := reflection_log_2780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2781_neg : (42785123 / 250000000) ≤ -Real.log (250000000000 / 296664363387) ∧
    -Real.log (250000000000 / 296664363387) ≤ (171140493 / 1000000000) := by
  have h := checkLog_sound (w := (46664363387 / 546664363387)) (n := 12)
    (lo := (42785123 / 250000000)) (hi := (171140493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296664363387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296664363387 / 250000000000) = 1/(250000000000 / 296664363387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2781 : Bounds (42785123 / 250000000) (171140493 / 1000000000) (Real.log (296664363387 / 250000000000)) := by
  have h := reflection_log_2781_neg
  have he : Real.log (296664363387 / 250000000000) = -Real.log (250000000000 / 296664363387) := by
    rw [show ((296664363387 / 250000000000) : ℝ) = ((250000000000 / 296664363387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2782_neg : (34317149 / 200000000) ≤ -Real.log (100000000000 / 118718593377) ∧
    -Real.log (100000000000 / 118718593377) ≤ (85792873 / 500000000) := by
  have h := checkLog_sound (w := (18718593377 / 218718593377)) (n := 12)
    (lo := (34317149 / 200000000)) (hi := (85792873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118718593377 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118718593377 / 100000000000) = 1/(100000000000 / 118718593377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2782 : Bounds (34317149 / 200000000) (85792873 / 500000000) (Real.log (118718593377 / 100000000000)) := by
  have h := reflection_log_2782_neg
  have he : Real.log (118718593377 / 100000000000) = -Real.log (100000000000 / 118718593377) := by
    rw [show ((118718593377 / 100000000000) : ℝ) = ((100000000000 / 118718593377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2783_neg : (343333327 / 1000000000) ≤ -Real.log (125000000000 / 176204819277) ∧
    -Real.log (125000000000 / 176204819277) ≤ (21458333 / 62500000) := by
  have h := checkLog_sound (w := (51204819277 / 301204819277)) (n := 12)
    (lo := (343333327 / 1000000000)) (hi := (21458333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176204819277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176204819277 / 125000000000) = 1/(125000000000 / 176204819277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2783 : Bounds (343333327 / 1000000000) (21458333 / 62500000) (Real.log (176204819277 / 125000000000)) := by
  have h := reflection_log_2783_neg
  have he : Real.log (176204819277 / 125000000000) = -Real.log (125000000000 / 176204819277) := by
    rw [show ((176204819277 / 125000000000) : ℝ) = ((125000000000 / 176204819277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2784_neg : (171769641 / 500000000) ≤ -Real.log (500000000000 / 704964453549) ∧
    -Real.log (500000000000 / 704964453549) ≤ (343539283 / 1000000000) := by
  have h := checkLog_sound (w := (204964453549 / 1204964453549)) (n := 12)
    (lo := (171769641 / 500000000)) (hi := (343539283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704964453549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704964453549 / 500000000000) = 1/(500000000000 / 704964453549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2784 : Bounds (171769641 / 500000000) (343539283 / 1000000000) (Real.log (704964453549 / 500000000000)) := by
  have h := reflection_log_2784_neg
  have he : Real.log (704964453549 / 500000000000) = -Real.log (500000000000 / 704964453549) := by
    rw [show ((704964453549 / 500000000000) : ℝ) = ((500000000000 / 704964453549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2785_neg : (78587337 / 500000000) ≤ -Real.log (5000 / 5851) ∧
    -Real.log (5000 / 5851) ≤ (6286987 / 40000000) := by
  have h := checkLog_sound (w := (851 / 10851)) (n := 12)
    (lo := (78587337 / 500000000)) (hi := (6286987 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5851 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5851 / 5000) = 1/(5000 / 5851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2785 : Bounds (78587337 / 500000000) (6286987 / 40000000) (Real.log (5851 / 5000)) := by
  have h := reflection_log_2785_neg
  have he : Real.log (5851 / 5000) = -Real.log (5000 / 5851) := by
    rw [show ((5851 / 5000) : ℝ) = ((5000 / 5851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2786_neg : (186570571 / 1000000000) ≤ -Real.log (4149 / 5000) ∧
    -Real.log (4149 / 5000) ≤ (46642643 / 250000000) := by
  have h := checkLog_sound (w := (851 / 9149)) (n := 12)
    (lo := (186570571 / 1000000000)) (hi := (46642643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4149) = 1/(4149 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2786 : Bounds (-46642643 / 250000000) (-186570571 / 1000000000) (Real.log (4149 / 5000)) := by
  have h := reflection_log_2786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2787_neg : (34037 / 200000000) ≤ -Real.log (5000000 / 5000851) ∧
    -Real.log (5000000 / 5000851) ≤ (85093 / 500000000) := by
  have h := checkLog_sound (w := (851 / 10000851)) (n := 12)
    (lo := (34037 / 200000000)) (hi := (85093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000851 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000851 / 5000000) = 1/(5000000 / 5000851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2787 : Bounds (34037 / 200000000) (85093 / 500000000) (Real.log (5000851 / 5000000)) := by
  have h := reflection_log_2787_neg
  have he : Real.log (5000851 / 5000000) = -Real.log (5000000 / 5000851) := by
    rw [show ((5000851 / 5000000) : ℝ) = ((5000000 / 5000851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2788_neg : (85107 / 500000000) ≤ -Real.log (4999149 / 5000000) ∧
    -Real.log (4999149 / 5000000) ≤ (34043 / 200000000) := by
  have h := checkLog_sound (w := (851 / 9999149)) (n := 12)
    (lo := (85107 / 500000000)) (hi := (34043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999149) = 1/(4999149 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2788 : Bounds (-34043 / 200000000) (-85107 / 500000000) (Real.log (4999149 / 5000000)) := by
  have h := reflection_log_2788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2789_neg : (40979819 / 500000000) ≤ -Real.log (250000 / 271353) ∧
    -Real.log (250000 / 271353) ≤ (81959639 / 1000000000) := by
  have h := checkLog_sound (w := (21353 / 521353)) (n := 12)
    (lo := (40979819 / 500000000)) (hi := (81959639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271353 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271353 / 250000) = 1/(250000 / 271353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2789 : Bounds (40979819 / 500000000) (81959639 / 1000000000) (Real.log (271353 / 250000)) := by
  have h := reflection_log_2789_neg
  have he : Real.log (271353 / 250000) = -Real.log (250000 / 271353) := by
    rw [show ((271353 / 250000) : ℝ) = ((250000 / 271353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2790_neg : (22320397 / 250000000) ≤ -Real.log (228647 / 250000) ∧
    -Real.log (228647 / 250000) ≤ (89281589 / 1000000000) := by
  have h := checkLog_sound (w := (21353 / 478647)) (n := 12)
    (lo := (22320397 / 250000000)) (hi := (89281589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228647) = 1/(228647 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2790 : Bounds (-89281589 / 1000000000) (-22320397 / 250000000) (Real.log (228647 / 250000)) := by
  have h := reflection_log_2790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2791_neg : (20541037 / 250000000) ≤ -Real.log (500000 / 542817) ∧
    -Real.log (500000 / 542817) ≤ (82164149 / 1000000000) := by
  have h := checkLog_sound (w := (42817 / 1042817)) (n := 12)
    (lo := (20541037 / 250000000)) (hi := (82164149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542817 / 500000) = 1/(500000 / 542817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2791 : Bounds (20541037 / 250000000) (82164149 / 1000000000) (Real.log (542817 / 500000)) := by
  have h := reflection_log_2791_neg
  have he : Real.log (542817 / 500000) = -Real.log (500000 / 542817) := by
    rw [show ((542817 / 500000) : ℝ) = ((500000 / 542817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2792_neg : (1790487 / 20000000) ≤ -Real.log (457183 / 500000) ∧
    -Real.log (457183 / 500000) ≤ (89524351 / 1000000000) := by
  have h := checkLog_sound (w := (42817 / 957183)) (n := 12)
    (lo := (1790487 / 20000000)) (hi := (89524351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457183) = 1/(457183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2792 : Bounds (-89524351 / 1000000000) (-1790487 / 20000000) (Real.log (457183 / 500000)) := by
  have h := reflection_log_2792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2793_neg : (7360201 / 1000000000) ≤ -Real.log (248166704511 / 250000000000) ∧
    -Real.log (248166704511 / 250000000000) ≤ (3680101 / 500000000) := by
  have h := checkLog_sound (w := (1833295489 / 498166704511)) (n := 12)
    (lo := (7360201 / 1000000000)) (hi := (3680101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248166704511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248166704511) = 1/(248166704511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2793 : Bounds (-3680101 / 500000000) (-7360201 / 1000000000) (Real.log (248166704511 / 250000000000)) := by
  have h := reflection_log_2793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2794_neg : (7321949 / 1000000000) ≤ -Real.log (62044049391 / 62500000000) ∧
    -Real.log (62044049391 / 62500000000) ≤ (146439 / 20000000) := by
  have h := checkLog_sound (w := (455950609 / 124544049391)) (n := 12)
    (lo := (7321949 / 1000000000)) (hi := (146439 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62044049391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62044049391) = 1/(62044049391 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2794 : Bounds (-146439 / 20000000) (-7321949 / 1000000000) (Real.log (62044049391 / 62500000000)) := by
  have h := reflection_log_2794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2795_neg : (85620613 / 500000000) ≤ -Real.log (500000000000 / 593388498427) ∧
    -Real.log (500000000000 / 593388498427) ≤ (171241227 / 1000000000) := by
  have h := checkLog_sound (w := (93388498427 / 1093388498427)) (n := 12)
    (lo := (85620613 / 500000000)) (hi := (171241227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593388498427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593388498427 / 500000000000) = 1/(500000000000 / 593388498427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2795 : Bounds (85620613 / 500000000) (171241227 / 1000000000) (Real.log (593388498427 / 500000000000)) := by
  have h := reflection_log_2795_neg
  have he : Real.log (593388498427 / 500000000000) = -Real.log (500000000000 / 593388498427) := by
    rw [show ((593388498427 / 500000000000) : ℝ) = ((500000000000 / 593388498427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2796_neg : (85844249 / 500000000) ≤ -Real.log (62500000000 / 74206745439) ∧
    -Real.log (62500000000 / 74206745439) ≤ (171688499 / 1000000000) := by
  have h := checkLog_sound (w := (11706745439 / 136706745439)) (n := 12)
    (lo := (85844249 / 500000000)) (hi := (171688499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74206745439 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74206745439 / 62500000000) = 1/(62500000000 / 74206745439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2796 : Bounds (85844249 / 500000000) (171688499 / 1000000000) (Real.log (74206745439 / 62500000000)) := by
  have h := reflection_log_2796_neg
  have he : Real.log (74206745439 / 62500000000) = -Real.log (62500000000 / 74206745439) := by
    rw [show ((74206745439 / 62500000000) : ℝ) = ((62500000000 / 74206745439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2797_neg : (171769641 / 500000000) ≤ -Real.log (125000000000 / 176241113387) ∧
    -Real.log (125000000000 / 176241113387) ≤ (343539283 / 1000000000) := by
  have h := checkLog_sound (w := (51241113387 / 301241113387)) (n := 12)
    (lo := (171769641 / 500000000)) (hi := (343539283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176241113387 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176241113387 / 125000000000) = 1/(125000000000 / 176241113387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2797 : Bounds (171769641 / 500000000) (343539283 / 1000000000) (Real.log (176241113387 / 125000000000)) := by
  have h := reflection_log_2797_neg
  have he : Real.log (176241113387 / 125000000000) = -Real.log (125000000000 / 176241113387) := by
    rw [show ((176241113387 / 125000000000) : ℝ) = ((125000000000 / 176241113387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2798_neg : (68749049 / 200000000) ≤ -Real.log (25000000000 / 35255483249) ∧
    -Real.log (25000000000 / 35255483249) ≤ (171872623 / 500000000) := by
  have h := checkLog_sound (w := (10255483249 / 60255483249)) (n := 12)
    (lo := (68749049 / 200000000)) (hi := (171872623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35255483249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35255483249 / 25000000000) = 1/(25000000000 / 35255483249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2798 : Bounds (68749049 / 200000000) (171872623 / 500000000) (Real.log (35255483249 / 25000000000)) := by
  have h := reflection_log_2798_neg
  have he : Real.log (35255483249 / 25000000000) = -Real.log (25000000000 / 35255483249) := by
    rw [show ((35255483249 / 25000000000) : ℝ) = ((25000000000 / 35255483249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2799_neg : (78630063 / 500000000) ≤ -Real.log (10000 / 11703) ∧
    -Real.log (10000 / 11703) ≤ (157260127 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 21703)) (n := 12)
    (lo := (78630063 / 500000000)) (hi := (157260127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 10000) = 1/(10000 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2799 : Bounds (78630063 / 500000000) (157260127 / 1000000000) (Real.log (11703 / 10000)) := by
  have h := reflection_log_2799_neg
  have he : Real.log (11703 / 10000) = -Real.log (10000 / 11703) := by
    rw [show ((11703 / 10000) : ℝ) = ((10000 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2800_neg : (186691089 / 1000000000) ≤ -Real.log (8297 / 10000) ∧
    -Real.log (8297 / 10000) ≤ (18669109 / 100000000) := by
  have h := checkLog_sound (w := (1703 / 18297)) (n := 12)
    (lo := (186691089 / 1000000000)) (hi := (18669109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8297) = 1/(8297 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2800 : Bounds (-18669109 / 100000000) (-186691089 / 1000000000) (Real.log (8297 / 10000)) := by
  have h := reflection_log_2800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2801_neg : (34057 / 200000000) ≤ -Real.log (10000000 / 10001703) ∧
    -Real.log (10000000 / 10001703) ≤ (85143 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 20001703)) (n := 12)
    (lo := (34057 / 200000000)) (hi := (85143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001703 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001703 / 10000000) = 1/(10000000 / 10001703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2801 : Bounds (34057 / 200000000) (85143 / 500000000) (Real.log (10001703 / 10000000)) := by
  have h := reflection_log_2801_neg
  have he : Real.log (10001703 / 10000000) = -Real.log (10000000 / 10001703) := by
    rw [show ((10001703 / 10000000) : ℝ) = ((10000000 / 10001703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2802_neg : (85157 / 500000000) ≤ -Real.log (9998297 / 10000000) ∧
    -Real.log (9998297 / 10000000) ≤ (34063 / 200000000) := by
  have h := checkLog_sound (w := (1703 / 19998297)) (n := 12)
    (lo := (85157 / 500000000)) (hi := (34063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998297) = 1/(9998297 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2802 : Bounds (-34063 / 200000000) (-85157 / 500000000) (Real.log (9998297 / 10000000)) := by
  have h := reflection_log_2802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2803_neg : (2562707 / 31250000) ≤ -Real.log (1000000 / 1085463) ∧
    -Real.log (1000000 / 1085463) ≤ (656053 / 8000000) := by
  have h := checkLog_sound (w := (85463 / 2085463)) (n := 12)
    (lo := (2562707 / 31250000)) (hi := (656053 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085463 / 1000000) = 1/(1000000 / 1085463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2803 : Bounds (2562707 / 31250000) (656053 / 8000000) (Real.log (1085463 / 1000000)) := by
  have h := reflection_log_2803_neg
  have he : Real.log (1085463 / 1000000) = -Real.log (1000000 / 1085463) := by
    rw [show ((1085463 / 1000000) : ℝ) = ((1000000 / 1085463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2804_neg : (11167169 / 125000000) ≤ -Real.log (914537 / 1000000) ∧
    -Real.log (914537 / 1000000) ≤ (89337353 / 1000000000) := by
  have h := checkLog_sound (w := (85463 / 1914537)) (n := 12)
    (lo := (11167169 / 125000000)) (hi := (89337353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914537) = 1/(914537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2804 : Bounds (-89337353 / 1000000000) (-11167169 / 125000000) (Real.log (914537 / 1000000)) := by
  have h := reflection_log_2804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2805_neg : (82210203 / 1000000000) ≤ -Real.log (250000 / 271421) ∧
    -Real.log (250000 / 271421) ≤ (20552551 / 250000000) := by
  have h := checkLog_sound (w := (21421 / 521421)) (n := 12)
    (lo := (82210203 / 1000000000)) (hi := (20552551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271421 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271421 / 250000) = 1/(250000 / 271421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2805 : Bounds (82210203 / 1000000000) (20552551 / 250000000) (Real.log (271421 / 250000)) := by
  have h := reflection_log_2805_neg
  have he : Real.log (271421 / 250000) = -Real.log (250000 / 271421) := by
    rw [show ((271421 / 250000) : ℝ) = ((250000 / 271421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2806_neg : (44789517 / 500000000) ≤ -Real.log (228579 / 250000) ∧
    -Real.log (228579 / 250000) ≤ (17915807 / 200000000) := by
  have h := checkLog_sound (w := (21421 / 478579)) (n := 12)
    (lo := (44789517 / 500000000)) (hi := (17915807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228579) = 1/(228579 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2806 : Bounds (-17915807 / 200000000) (-44789517 / 500000000) (Real.log (228579 / 250000)) := by
  have h := reflection_log_2806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2807_neg : (7368831 / 1000000000) ≤ -Real.log (62041140759 / 62500000000) ∧
    -Real.log (62041140759 / 62500000000) ≤ (57569 / 7812500) := by
  have h := checkLog_sound (w := (458859241 / 124541140759)) (n := 12)
    (lo := (7368831 / 1000000000)) (hi := (57569 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62041140759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62041140759) = 1/(62041140759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2807 : Bounds (-57569 / 7812500) (-7368831 / 1000000000) (Real.log (62041140759 / 62500000000)) := by
  have h := reflection_log_2807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2808_neg : (916341 / 125000000) ≤ -Real.log (992696075631 / 1000000000000) ∧
    -Real.log (992696075631 / 1000000000000) ≤ (7330729 / 1000000000) := by
  have h := checkLog_sound (w := (7303924369 / 1992696075631)) (n := 12)
    (lo := (916341 / 125000000)) (hi := (7330729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992696075631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992696075631) = 1/(992696075631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2808 : Bounds (-7330729 / 1000000000) (-916341 / 125000000) (Real.log (992696075631 / 1000000000000)) := by
  have h := reflection_log_2808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2809_neg : (21417997 / 125000000) ≤ -Real.log (250000000000 / 296724736123) ∧
    -Real.log (250000000000 / 296724736123) ≤ (171343977 / 1000000000) := by
  have h := checkLog_sound (w := (46724736123 / 546724736123)) (n := 12)
    (lo := (21417997 / 125000000)) (hi := (171343977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296724736123 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296724736123 / 250000000000) = 1/(250000000000 / 296724736123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2809 : Bounds (21417997 / 125000000) (171343977 / 1000000000) (Real.log (296724736123 / 250000000000)) := by
  have h := reflection_log_2809_neg
  have he : Real.log (296724736123 / 250000000000) = -Real.log (250000000000 / 296724736123) := by
    rw [show ((296724736123 / 250000000000) : ℝ) = ((250000000000 / 296724736123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2810_neg : (171789237 / 1000000000) ≤ -Real.log (125000000000 / 148428442683) ∧
    -Real.log (125000000000 / 148428442683) ≤ (85894619 / 500000000) := by
  have h := checkLog_sound (w := (23428442683 / 273428442683)) (n := 12)
    (lo := (171789237 / 1000000000)) (hi := (85894619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148428442683 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148428442683 / 125000000000) = 1/(125000000000 / 148428442683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2810 : Bounds (171789237 / 1000000000) (85894619 / 500000000) (Real.log (148428442683 / 125000000000)) := by
  have h := reflection_log_2810_neg
  have he : Real.log (148428442683 / 125000000000) = -Real.log (125000000000 / 148428442683) := by
    rw [show ((148428442683 / 125000000000) : ℝ) = ((125000000000 / 148428442683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2811_neg : (68749049 / 200000000) ≤ -Real.log (500000000000 / 705109664979) ∧
    -Real.log (500000000000 / 705109664979) ≤ (171872623 / 500000000) := by
  have h := checkLog_sound (w := (205109664979 / 1205109664979)) (n := 12)
    (lo := (68749049 / 200000000)) (hi := (171872623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705109664979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705109664979 / 500000000000) = 1/(500000000000 / 705109664979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2811 : Bounds (68749049 / 200000000) (171872623 / 500000000) (Real.log (705109664979 / 500000000000)) := by
  have h := reflection_log_2811_neg
  have he : Real.log (705109664979 / 500000000000) = -Real.log (500000000000 / 705109664979) := by
    rw [show ((705109664979 / 500000000000) : ℝ) = ((500000000000 / 705109664979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2812_neg : (68790243 / 200000000) ≤ -Real.log (250000000000 / 352627455707) ∧
    -Real.log (250000000000 / 352627455707) ≤ (21496951 / 62500000) := by
  have h := checkLog_sound (w := (102627455707 / 602627455707)) (n := 12)
    (lo := (68790243 / 200000000)) (hi := (21496951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352627455707 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352627455707 / 250000000000) = 1/(250000000000 / 352627455707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2812 : Bounds (68790243 / 200000000) (21496951 / 62500000) (Real.log (352627455707 / 250000000000)) := by
  have h := reflection_log_2812_neg
  have he : Real.log (352627455707 / 250000000000) = -Real.log (250000000000 / 352627455707) := by
    rw [show ((352627455707 / 250000000000) : ℝ) = ((250000000000 / 352627455707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2813_neg : (15734557 / 100000000) ≤ -Real.log (1250 / 1463) ∧
    -Real.log (1250 / 1463) ≤ (157345571 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 2713)) (n := 12)
    (lo := (15734557 / 100000000)) (hi := (157345571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1250) = 1/(1250 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2813 : Bounds (15734557 / 100000000) (157345571 / 1000000000) (Real.log (1463 / 1250)) := by
  have h := reflection_log_2813_neg
  have he : Real.log (1463 / 1250) = -Real.log (1250 / 1463) := by
    rw [show ((1463 / 1250) : ℝ) = ((1250 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2814_neg : (93405811 / 500000000) ≤ -Real.log (1037 / 1250) ∧
    -Real.log (1037 / 1250) ≤ (186811623 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 2287)) (n := 12)
    (lo := (93405811 / 500000000)) (hi := (186811623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1037) = 1/(1037 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2814 : Bounds (-186811623 / 1000000000) (-93405811 / 500000000) (Real.log (1037 / 1250)) := by
  have h := reflection_log_2814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2815_neg : (34077 / 200000000) ≤ -Real.log (1250000 / 1250213) ∧
    -Real.log (1250000 / 1250213) ≤ (85193 / 500000000) := by
  have h := checkLog_sound (w := (213 / 2500213)) (n := 12)
    (lo := (34077 / 200000000)) (hi := (85193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250213 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250213 / 1250000) = 1/(1250000 / 1250213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2815 : Bounds (34077 / 200000000) (85193 / 500000000) (Real.log (1250213 / 1250000)) := by
  have h := reflection_log_2815_neg
  have he : Real.log (1250213 / 1250000) = -Real.log (1250000 / 1250213) := by
    rw [show ((1250213 / 1250000) : ℝ) = ((1250000 / 1250213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0044 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2816_neg : (85207 / 500000000) ≤ -Real.log (1249787 / 1250000) ∧
    -Real.log (1249787 / 1250000) ≤ (34083 / 200000000) := by
  have h := checkLog_sound (w := (213 / 2499787)) (n := 12)
    (lo := (85207 / 500000000)) (hi := (34083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249787) = 1/(1249787 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2816 : Bounds (-34083 / 200000000) (-85207 / 500000000) (Real.log (1249787 / 1250000)) := by
  have h := reflection_log_2816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2817_neg : (82053607 / 1000000000) ≤ -Real.log (500000 / 542757) ∧
    -Real.log (500000 / 542757) ≤ (10256701 / 125000000) := by
  have h := checkLog_sound (w := (42757 / 1042757)) (n := 12)
    (lo := (82053607 / 1000000000)) (hi := (10256701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542757 / 500000) = 1/(500000 / 542757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2817 : Bounds (82053607 / 1000000000) (10256701 / 125000000) (Real.log (542757 / 500000)) := by
  have h := reflection_log_2817_neg
  have he : Real.log (542757 / 500000) = -Real.log (500000 / 542757) := by
    rw [show ((542757 / 500000) : ℝ) = ((500000 / 542757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2818_neg : (558707 / 6250000) ≤ -Real.log (457243 / 500000) ∧
    -Real.log (457243 / 500000) ≤ (89393121 / 1000000000) := by
  have h := checkLog_sound (w := (42757 / 957243)) (n := 12)
    (lo := (558707 / 6250000)) (hi := (89393121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457243) = 1/(457243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2818 : Bounds (-89393121 / 1000000000) (-558707 / 6250000) (Real.log (457243 / 500000)) := by
  have h := reflection_log_2818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2819_neg : (82257177 / 1000000000) ≤ -Real.log (200000 / 217147) ∧
    -Real.log (200000 / 217147) ≤ (41128589 / 500000000) := by
  have h := checkLog_sound (w := (17147 / 417147)) (n := 12)
    (lo := (82257177 / 1000000000)) (hi := (41128589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217147 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217147 / 200000) = 1/(200000 / 217147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2819 : Bounds (82257177 / 1000000000) (41128589 / 500000000) (Real.log (217147 / 200000)) := by
  have h := reflection_log_2819_neg
  have he : Real.log (217147 / 200000) = -Real.log (200000 / 217147) := by
    rw [show ((217147 / 200000) : ℝ) = ((200000 / 217147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2820_neg : (17926963 / 200000000) ≤ -Real.log (182853 / 200000) ∧
    -Real.log (182853 / 200000) ≤ (175068 / 1953125) := by
  have h := checkLog_sound (w := (17147 / 382853)) (n := 12)
    (lo := (17926963 / 200000000)) (hi := (175068 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182853) = 1/(182853 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2820 : Bounds (-175068 / 1953125) (-17926963 / 200000000) (Real.log (182853 / 200000)) := by
  have h := reflection_log_2820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2821_neg : (3688819 / 500000000) ≤ -Real.log (39705980391 / 40000000000) ∧
    -Real.log (39705980391 / 40000000000) ≤ (7377639 / 1000000000) := by
  have h := checkLog_sound (w := (294019609 / 79705980391)) (n := 12)
    (lo := (3688819 / 500000000)) (hi := (7377639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39705980391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39705980391) = 1/(39705980391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2821 : Bounds (-7377639 / 1000000000) (-3688819 / 500000000) (Real.log (39705980391 / 40000000000)) := by
  have h := reflection_log_2821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2822_neg : (917439 / 125000000) ≤ -Real.log (248171838951 / 250000000000) ∧
    -Real.log (248171838951 / 250000000000) ≤ (7339513 / 1000000000) := by
  have h := checkLog_sound (w := (1828161049 / 498171838951)) (n := 12)
    (lo := (917439 / 125000000)) (hi := (7339513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248171838951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248171838951) = 1/(248171838951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2822 : Bounds (-7339513 / 1000000000) (-917439 / 125000000) (Real.log (248171838951 / 250000000000)) := by
  have h := reflection_log_2822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2823_neg : (171446727 / 1000000000) ≤ -Real.log (250000000000 / 296755226433) ∧
    -Real.log (250000000000 / 296755226433) ≤ (21430841 / 125000000) := by
  have h := checkLog_sound (w := (46755226433 / 546755226433)) (n := 12)
    (lo := (171446727 / 1000000000)) (hi := (21430841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296755226433 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296755226433 / 250000000000) = 1/(250000000000 / 296755226433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2823 : Bounds (171446727 / 1000000000) (21430841 / 125000000) (Real.log (296755226433 / 250000000000)) := by
  have h := reflection_log_2823_neg
  have he : Real.log (296755226433 / 250000000000) = -Real.log (250000000000 / 296755226433) := by
    rw [show ((296755226433 / 250000000000) : ℝ) = ((250000000000 / 296755226433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2824_neg : (21486499 / 125000000) ≤ -Real.log (100000000000 / 118754956167) ∧
    -Real.log (100000000000 / 118754956167) ≤ (171891993 / 1000000000) := by
  have h := checkLog_sound (w := (18754956167 / 218754956167)) (n := 12)
    (lo := (21486499 / 125000000)) (hi := (171891993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118754956167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118754956167 / 100000000000) = 1/(100000000000 / 118754956167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2824 : Bounds (21486499 / 125000000) (171891993 / 1000000000) (Real.log (118754956167 / 100000000000)) := by
  have h := reflection_log_2824_neg
  have he : Real.log (118754956167 / 100000000000) = -Real.log (100000000000 / 118754956167) := by
    rw [show ((118754956167 / 100000000000) : ℝ) = ((100000000000 / 118754956167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2825_neg : (68790243 / 200000000) ≤ -Real.log (500000000000 / 705254911413) ∧
    -Real.log (500000000000 / 705254911413) ≤ (21496951 / 62500000) := by
  have h := checkLog_sound (w := (205254911413 / 1205254911413)) (n := 12)
    (lo := (68790243 / 200000000)) (hi := (21496951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705254911413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705254911413 / 500000000000) = 1/(500000000000 / 705254911413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2825 : Bounds (68790243 / 200000000) (21496951 / 62500000) (Real.log (705254911413 / 500000000000)) := by
  have h := reflection_log_2825_neg
  have he : Real.log (705254911413 / 500000000000) = -Real.log (500000000000 / 705254911413) := by
    rw [show ((705254911413 / 500000000000) : ℝ) = ((500000000000 / 705254911413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2826_neg : (43019649 / 125000000) ≤ -Real.log (100000000000 / 141080038573) ∧
    -Real.log (100000000000 / 141080038573) ≤ (344157193 / 1000000000) := by
  have h := checkLog_sound (w := (41080038573 / 241080038573)) (n := 12)
    (lo := (43019649 / 125000000)) (hi := (344157193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141080038573 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141080038573 / 100000000000) = 1/(100000000000 / 141080038573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2826 : Bounds (43019649 / 125000000) (344157193 / 1000000000) (Real.log (141080038573 / 100000000000)) := by
  have h := reflection_log_2826_neg
  have he : Real.log (141080038573 / 100000000000) = -Real.log (100000000000 / 141080038573) := by
    rw [show ((141080038573 / 100000000000) : ℝ) = ((100000000000 / 141080038573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2827_neg : (157431007 / 1000000000) ≤ -Real.log (2000 / 2341) ∧
    -Real.log (2000 / 2341) ≤ (4919719 / 31250000) := by
  have h := checkLog_sound (w := (341 / 4341)) (n := 12)
    (lo := (157431007 / 1000000000)) (hi := (4919719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2341 / 2000) = 1/(2000 / 2341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2827 : Bounds (157431007 / 1000000000) (4919719 / 31250000) (Real.log (2341 / 2000)) := by
  have h := reflection_log_2827_neg
  have he : Real.log (2341 / 2000) = -Real.log (2000 / 2341) := by
    rw [show ((2341 / 2000) : ℝ) = ((2000 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2828_neg : (186932169 / 1000000000) ≤ -Real.log (1659 / 2000) ∧
    -Real.log (1659 / 2000) ≤ (18693217 / 100000000) := by
  have h := checkLog_sound (w := (341 / 3659)) (n := 12)
    (lo := (186932169 / 1000000000)) (hi := (18693217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1659) = 1/(1659 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2828 : Bounds (-18693217 / 100000000) (-186932169 / 1000000000) (Real.log (1659 / 2000)) := by
  have h := reflection_log_2828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2829_neg : (34097 / 200000000) ≤ -Real.log (2000000 / 2000341) ∧
    -Real.log (2000000 / 2000341) ≤ (85243 / 500000000) := by
  have h := checkLog_sound (w := (341 / 4000341)) (n := 12)
    (lo := (34097 / 200000000)) (hi := (85243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000341 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000341 / 2000000) = 1/(2000000 / 2000341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2829 : Bounds (34097 / 200000000) (85243 / 500000000) (Real.log (2000341 / 2000000)) := by
  have h := reflection_log_2829_neg
  have he : Real.log (2000341 / 2000000) = -Real.log (2000000 / 2000341) := by
    rw [show ((2000341 / 2000000) : ℝ) = ((2000000 / 2000341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2830_neg : (85257 / 500000000) ≤ -Real.log (1999659 / 2000000) ∧
    -Real.log (1999659 / 2000000) ≤ (34103 / 200000000) := by
  have h := checkLog_sound (w := (341 / 3999659)) (n := 12)
    (lo := (85257 / 500000000)) (hi := (34103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999659) = 1/(1999659 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2830 : Bounds (-34103 / 200000000) (-85257 / 500000000) (Real.log (1999659 / 2000000)) := by
  have h := reflection_log_2830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2831_neg : (20525147 / 250000000) ≤ -Real.log (200000 / 217113) ∧
    -Real.log (200000 / 217113) ≤ (82100589 / 1000000000) := by
  have h := checkLog_sound (w := (17113 / 417113)) (n := 12)
    (lo := (20525147 / 250000000)) (hi := (82100589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217113 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217113 / 200000) = 1/(200000 / 217113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2831 : Bounds (20525147 / 250000000) (82100589 / 1000000000) (Real.log (217113 / 200000)) := by
  have h := reflection_log_2831_neg
  have he : Real.log (217113 / 200000) = -Real.log (200000 / 217113) := by
    rw [show ((217113 / 200000) : ℝ) = ((200000 / 217113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2832_neg : (8944889 / 100000000) ≤ -Real.log (182887 / 200000) ∧
    -Real.log (182887 / 200000) ≤ (89448891 / 1000000000) := by
  have h := checkLog_sound (w := (17113 / 382887)) (n := 12)
    (lo := (8944889 / 100000000)) (hi := (89448891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182887) = 1/(182887 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2832 : Bounds (-89448891 / 1000000000) (-8944889 / 100000000) (Real.log (182887 / 200000)) := by
  have h := reflection_log_2832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2833_neg : (20576037 / 250000000) ≤ -Real.log (500000 / 542893) ∧
    -Real.log (500000 / 542893) ≤ (82304149 / 1000000000) := by
  have h := checkLog_sound (w := (42893 / 1042893)) (n := 12)
    (lo := (20576037 / 250000000)) (hi := (82304149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542893 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542893 / 500000) = 1/(500000 / 542893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2833 : Bounds (20576037 / 250000000) (82304149 / 1000000000) (Real.log (542893 / 500000)) := by
  have h := reflection_log_2833_neg
  have he : Real.log (542893 / 500000) = -Real.log (500000 / 542893) := by
    rw [show ((542893 / 500000) : ℝ) = ((500000 / 542893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2834_neg : (89690599 / 1000000000) ≤ -Real.log (457107 / 500000) ∧
    -Real.log (457107 / 500000) ≤ (448453 / 5000000) := by
  have h := checkLog_sound (w := (42893 / 957107)) (n := 12)
    (lo := (89690599 / 1000000000)) (hi := (448453 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457107) = 1/(457107 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2834 : Bounds (-448453 / 5000000) (-89690599 / 1000000000) (Real.log (457107 / 500000)) := by
  have h := reflection_log_2834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2835_neg : (147729 / 20000000) ≤ -Real.log (248160190551 / 250000000000) ∧
    -Real.log (248160190551 / 250000000000) ≤ (7386451 / 1000000000) := by
  have h := checkLog_sound (w := (1839809449 / 498160190551)) (n := 12)
    (lo := (147729 / 20000000)) (hi := (7386451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248160190551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248160190551) = 1/(248160190551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2835 : Bounds (-7386451 / 1000000000) (-147729 / 20000000) (Real.log (248160190551 / 250000000000)) := by
  have h := reflection_log_2835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2836_neg : (7348301 / 1000000000) ≤ -Real.log (39707145231 / 40000000000) ∧
    -Real.log (39707145231 / 40000000000) ≤ (3674151 / 500000000) := by
  have h := checkLog_sound (w := (292854769 / 79707145231)) (n := 12)
    (lo := (7348301 / 1000000000)) (hi := (3674151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39707145231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39707145231) = 1/(39707145231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2836 : Bounds (-3674151 / 500000000) (-7348301 / 1000000000) (Real.log (39707145231 / 40000000000)) := by
  have h := reflection_log_2836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2837_neg : (171549479 / 1000000000) ≤ -Real.log (15625000000 / 18549107509) ∧
    -Real.log (15625000000 / 18549107509) ≤ (4288737 / 25000000) := by
  have h := checkLog_sound (w := (2924107509 / 34174107509)) (n := 12)
    (lo := (171549479 / 1000000000)) (hi := (4288737 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18549107509 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18549107509 / 15625000000) = 1/(15625000000 / 18549107509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2837 : Bounds (171549479 / 1000000000) (4288737 / 25000000) (Real.log (18549107509 / 15625000000)) := by
  have h := reflection_log_2837_neg
  have he : Real.log (18549107509 / 15625000000) = -Real.log (15625000000 / 18549107509) := by
    rw [show ((18549107509 / 15625000000) : ℝ) = ((15625000000 / 18549107509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2838_neg : (171994747 / 1000000000) ≤ -Real.log (250000000000 / 296917898873) ∧
    -Real.log (250000000000 / 296917898873) ≤ (42998687 / 250000000) := by
  have h := checkLog_sound (w := (46917898873 / 546917898873)) (n := 12)
    (lo := (171994747 / 1000000000)) (hi := (42998687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296917898873 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296917898873 / 250000000000) = 1/(250000000000 / 296917898873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2838 : Bounds (171994747 / 1000000000) (42998687 / 250000000) (Real.log (296917898873 / 250000000000)) := by
  have h := reflection_log_2838_neg
  have he : Real.log (296917898873 / 250000000000) = -Real.log (250000000000 / 296917898873) := by
    rw [show ((296917898873 / 250000000000) : ℝ) = ((250000000000 / 296917898873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2839_neg : (43019649 / 125000000) ≤ -Real.log (15625000000 / 22043756027) ∧
    -Real.log (15625000000 / 22043756027) ≤ (344157193 / 1000000000) := by
  have h := checkLog_sound (w := (6418756027 / 37668756027)) (n := 12)
    (lo := (43019649 / 125000000)) (hi := (344157193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22043756027 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22043756027 / 15625000000) = 1/(15625000000 / 22043756027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2839 : Bounds (43019649 / 125000000) (344157193 / 1000000000) (Real.log (22043756027 / 15625000000)) := by
  have h := reflection_log_2839_neg
  have he : Real.log (22043756027 / 15625000000) = -Real.log (15625000000 / 22043756027) := by
    rw [show ((22043756027 / 15625000000) : ℝ) = ((15625000000 / 22043756027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2840_neg : (344363177 / 1000000000) ≤ -Real.log (500000000000 / 705545509343) ∧
    -Real.log (500000000000 / 705545509343) ≤ (172181589 / 500000000) := by
  have h := checkLog_sound (w := (205545509343 / 1205545509343)) (n := 12)
    (lo := (344363177 / 1000000000)) (hi := (172181589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705545509343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705545509343 / 500000000000) = 1/(500000000000 / 705545509343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2840 : Bounds (344363177 / 1000000000) (172181589 / 500000000) (Real.log (705545509343 / 500000000000)) := by
  have h := reflection_log_2840_neg
  have he : Real.log (705545509343 / 500000000000) = -Real.log (500000000000 / 705545509343) := by
    rw [show ((705545509343 / 500000000000) : ℝ) = ((500000000000 / 705545509343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2841_neg : (157516437 / 1000000000) ≤ -Real.log (5000 / 5853) ∧
    -Real.log (5000 / 5853) ≤ (78758219 / 500000000) := by
  have h := checkLog_sound (w := (853 / 10853)) (n := 12)
    (lo := (157516437 / 1000000000)) (hi := (78758219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5853 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5853 / 5000) = 1/(5000 / 5853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2841 : Bounds (157516437 / 1000000000) (78758219 / 500000000) (Real.log (5853 / 5000)) := by
  have h := reflection_log_2841_neg
  have he : Real.log (5853 / 5000) = -Real.log (5000 / 5853) := by
    rw [show ((5853 / 5000) : ℝ) = ((5000 / 5853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2842_neg : (187052731 / 1000000000) ≤ -Real.log (4147 / 5000) ∧
    -Real.log (4147 / 5000) ≤ (46763183 / 250000000) := by
  have h := checkLog_sound (w := (853 / 9147)) (n := 12)
    (lo := (187052731 / 1000000000)) (hi := (46763183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4147) = 1/(4147 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2842 : Bounds (-46763183 / 250000000) (-187052731 / 1000000000) (Real.log (4147 / 5000)) := by
  have h := reflection_log_2842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2843_neg : (34117 / 200000000) ≤ -Real.log (5000000 / 5000853) ∧
    -Real.log (5000000 / 5000853) ≤ (85293 / 500000000) := by
  have h := checkLog_sound (w := (853 / 10000853)) (n := 12)
    (lo := (34117 / 200000000)) (hi := (85293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000853 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000853 / 5000000) = 1/(5000000 / 5000853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2843 : Bounds (34117 / 200000000) (85293 / 500000000) (Real.log (5000853 / 5000000)) := by
  have h := reflection_log_2843_neg
  have he : Real.log (5000853 / 5000000) = -Real.log (5000000 / 5000853) := by
    rw [show ((5000853 / 5000000) : ℝ) = ((5000000 / 5000853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2844_neg : (85307 / 500000000) ≤ -Real.log (4999147 / 5000000) ∧
    -Real.log (4999147 / 5000000) ≤ (34123 / 200000000) := by
  have h := checkLog_sound (w := (853 / 9999147)) (n := 12)
    (lo := (85307 / 500000000)) (hi := (34123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999147) = 1/(4999147 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2844 : Bounds (-34123 / 200000000) (-85307 / 500000000) (Real.log (4999147 / 5000000)) := by
  have h := reflection_log_2844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2845_neg : (41073323 / 500000000) ≤ -Real.log (200000 / 217123) ∧
    -Real.log (200000 / 217123) ≤ (82146647 / 1000000000) := by
  have h := checkLog_sound (w := (17123 / 417123)) (n := 12)
    (lo := (41073323 / 500000000)) (hi := (82146647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217123 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217123 / 200000) = 1/(200000 / 217123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2845 : Bounds (41073323 / 500000000) (82146647 / 1000000000) (Real.log (217123 / 200000)) := by
  have h := reflection_log_2845_neg
  have he : Real.log (217123 / 200000) = -Real.log (200000 / 217123) := by
    rw [show ((217123 / 200000) : ℝ) = ((200000 / 217123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2846_neg : (8950357 / 100000000) ≤ -Real.log (182877 / 200000) ∧
    -Real.log (182877 / 200000) ≤ (89503571 / 1000000000) := by
  have h := checkLog_sound (w := (17123 / 382877)) (n := 12)
    (lo := (8950357 / 100000000)) (hi := (89503571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182877) = 1/(182877 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2846 : Bounds (-89503571 / 1000000000) (-8950357 / 100000000) (Real.log (182877 / 200000)) := by
  have h := reflection_log_2846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2847_neg : (41175559 / 500000000) ≤ -Real.log (1000000 / 1085837) ∧
    -Real.log (1000000 / 1085837) ≤ (82351119 / 1000000000) := by
  have h := checkLog_sound (w := (85837 / 2085837)) (n := 12)
    (lo := (41175559 / 500000000)) (hi := (82351119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085837 / 1000000) = 1/(1000000 / 1085837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2847 : Bounds (41175559 / 500000000) (82351119 / 1000000000) (Real.log (1085837 / 1000000)) := by
  have h := reflection_log_2847_neg
  have he : Real.log (1085837 / 1000000) = -Real.log (1000000 / 1085837) := by
    rw [show ((1085837 / 1000000) : ℝ) = ((1000000 / 1085837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2848_neg : (44873193 / 500000000) ≤ -Real.log (914163 / 1000000) ∧
    -Real.log (914163 / 1000000) ≤ (89746387 / 1000000000) := by
  have h := checkLog_sound (w := (85837 / 1914163)) (n := 12)
    (lo := (44873193 / 500000000)) (hi := (89746387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914163) = 1/(914163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2848 : Bounds (-89746387 / 1000000000) (-44873193 / 500000000) (Real.log (914163 / 1000000)) := by
  have h := reflection_log_2848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2849_neg : (1848817 / 250000000) ≤ -Real.log (992632009431 / 1000000000000) ∧
    -Real.log (992632009431 / 1000000000000) ≤ (7395269 / 1000000000) := by
  have h := checkLog_sound (w := (7367990569 / 1992632009431)) (n := 12)
    (lo := (1848817 / 250000000)) (hi := (7395269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992632009431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992632009431) = 1/(992632009431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2849 : Bounds (-7395269 / 1000000000) (-1848817 / 250000000) (Real.log (992632009431 / 1000000000000)) := by
  have h := reflection_log_2849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2850_neg : (1839231 / 250000000) ≤ -Real.log (39706802871 / 40000000000) ∧
    -Real.log (39706802871 / 40000000000) ≤ (294277 / 40000000) := by
  have h := checkLog_sound (w := (293197129 / 79706802871)) (n := 12)
    (lo := (1839231 / 250000000)) (hi := (294277 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39706802871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39706802871) = 1/(39706802871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2850 : Bounds (-294277 / 40000000) (-1839231 / 250000000) (Real.log (39706802871 / 40000000000)) := by
  have h := reflection_log_2850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2851_neg : (171650217 / 1000000000) ≤ -Real.log (250000000000 / 296815619241) ∧
    -Real.log (250000000000 / 296815619241) ≤ (85825109 / 500000000) := by
  have h := checkLog_sound (w := (46815619241 / 546815619241)) (n := 12)
    (lo := (171650217 / 1000000000)) (hi := (85825109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296815619241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296815619241 / 250000000000) = 1/(250000000000 / 296815619241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2851 : Bounds (171650217 / 1000000000) (85825109 / 500000000) (Real.log (296815619241 / 250000000000)) := by
  have h := reflection_log_2851_neg
  have he : Real.log (296815619241 / 250000000000) = -Real.log (250000000000 / 296815619241) := by
    rw [show ((296815619241 / 250000000000) : ℝ) = ((250000000000 / 296815619241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2852_neg : (5378047 / 31250000) ≤ -Real.log (100000000000 / 118779364293) ∧
    -Real.log (100000000000 / 118779364293) ≤ (34419501 / 200000000) := by
  have h := checkLog_sound (w := (18779364293 / 218779364293)) (n := 12)
    (lo := (5378047 / 31250000)) (hi := (34419501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118779364293 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118779364293 / 100000000000) = 1/(100000000000 / 118779364293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2852 : Bounds (5378047 / 31250000) (34419501 / 200000000) (Real.log (118779364293 / 100000000000)) := by
  have h := reflection_log_2852_neg
  have he : Real.log (118779364293 / 100000000000) = -Real.log (100000000000 / 118779364293) := by
    rw [show ((118779364293 / 100000000000) : ℝ) = ((100000000000 / 118779364293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2853_neg : (344363177 / 1000000000) ≤ -Real.log (250000000000 / 352772754671) ∧
    -Real.log (250000000000 / 352772754671) ≤ (172181589 / 500000000) := by
  have h := checkLog_sound (w := (102772754671 / 602772754671)) (n := 12)
    (lo := (344363177 / 1000000000)) (hi := (172181589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352772754671 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352772754671 / 250000000000) = 1/(250000000000 / 352772754671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2853 : Bounds (344363177 / 1000000000) (172181589 / 500000000) (Real.log (352772754671 / 250000000000)) := by
  have h := reflection_log_2853_neg
  have he : Real.log (352772754671 / 250000000000) = -Real.log (250000000000 / 352772754671) := by
    rw [show ((352772754671 / 250000000000) : ℝ) = ((250000000000 / 352772754671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2854_neg : (344569169 / 1000000000) ≤ -Real.log (7812500000 / 11026419701) ∧
    -Real.log (7812500000 / 11026419701) ≤ (34456917 / 100000000) := by
  have h := checkLog_sound (w := (3213919701 / 18838919701)) (n := 12)
    (lo := (344569169 / 1000000000)) (hi := (34456917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11026419701 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11026419701 / 7812500000) = 1/(7812500000 / 11026419701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2854 : Bounds (344569169 / 1000000000) (34456917 / 100000000) (Real.log (11026419701 / 7812500000)) := by
  have h := reflection_log_2854_neg
  have he : Real.log (11026419701 / 7812500000) = -Real.log (7812500000 / 11026419701) := by
    rw [show ((11026419701 / 7812500000) : ℝ) = ((7812500000 / 11026419701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2855_neg : (7880093 / 50000000) ≤ -Real.log (10000 / 11707) ∧
    -Real.log (10000 / 11707) ≤ (157601861 / 1000000000) := by
  have h := checkLog_sound (w := (1707 / 21707)) (n := 12)
    (lo := (7880093 / 50000000)) (hi := (157601861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11707 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11707 / 10000) = 1/(10000 / 11707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2855 : Bounds (7880093 / 50000000) (157601861 / 1000000000) (Real.log (11707 / 10000)) := by
  have h := reflection_log_2855_neg
  have he : Real.log (11707 / 10000) = -Real.log (10000 / 11707) := by
    rw [show ((11707 / 10000) : ℝ) = ((10000 / 11707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2856_neg : (187173307 / 1000000000) ≤ -Real.log (8293 / 10000) ∧
    -Real.log (8293 / 10000) ≤ (46793327 / 250000000) := by
  have h := checkLog_sound (w := (1707 / 18293)) (n := 12)
    (lo := (187173307 / 1000000000)) (hi := (46793327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8293) = 1/(8293 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2856 : Bounds (-46793327 / 250000000) (-187173307 / 1000000000) (Real.log (8293 / 10000)) := by
  have h := reflection_log_2856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2857_neg : (34137 / 200000000) ≤ -Real.log (10000000 / 10001707) ∧
    -Real.log (10000000 / 10001707) ≤ (85343 / 500000000) := by
  have h := checkLog_sound (w := (1707 / 20001707)) (n := 12)
    (lo := (34137 / 200000000)) (hi := (85343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001707 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001707 / 10000000) = 1/(10000000 / 10001707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2857 : Bounds (34137 / 200000000) (85343 / 500000000) (Real.log (10001707 / 10000000)) := by
  have h := reflection_log_2857_neg
  have he : Real.log (10001707 / 10000000) = -Real.log (10000000 / 10001707) := by
    rw [show ((10001707 / 10000000) : ℝ) = ((10000000 / 10001707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2858_neg : (85357 / 500000000) ≤ -Real.log (9998293 / 10000000) ∧
    -Real.log (9998293 / 10000000) ≤ (34143 / 200000000) := by
  have h := checkLog_sound (w := (1707 / 19998293)) (n := 12)
    (lo := (85357 / 500000000)) (hi := (34143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998293) = 1/(9998293 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2858 : Bounds (-34143 / 200000000) (-85357 / 500000000) (Real.log (9998293 / 10000000)) := by
  have h := reflection_log_2858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2859_neg : (82193623 / 1000000000) ≤ -Real.log (500000 / 542833) ∧
    -Real.log (500000 / 542833) ≤ (10274203 / 125000000) := by
  have h := checkLog_sound (w := (42833 / 1042833)) (n := 12)
    (lo := (82193623 / 1000000000)) (hi := (10274203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542833 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542833 / 500000) = 1/(500000 / 542833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2859 : Bounds (82193623 / 1000000000) (10274203 / 125000000) (Real.log (542833 / 500000)) := by
  have h := reflection_log_2859_neg
  have he : Real.log (542833 / 500000) = -Real.log (500000 / 542833) := by
    rw [show ((542833 / 500000) : ℝ) = ((500000 / 542833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2860_neg : (89559347 / 1000000000) ≤ -Real.log (457167 / 500000) ∧
    -Real.log (457167 / 500000) ≤ (22389837 / 250000000) := by
  have h := checkLog_sound (w := (42833 / 957167)) (n := 12)
    (lo := (89559347 / 1000000000)) (hi := (22389837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457167) = 1/(457167 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2860 : Bounds (-22389837 / 250000000) (-89559347 / 1000000000) (Real.log (457167 / 500000)) := by
  have h := reflection_log_2860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2861_neg : (16479617 / 200000000) ≤ -Real.log (15625 / 16967) ∧
    -Real.log (15625 / 16967) ≤ (41199043 / 500000000) := by
  have h := checkLog_sound (w := (671 / 16296)) (n := 12)
    (lo := (16479617 / 200000000)) (hi := (41199043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16967 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16967 / 15625) = 1/(15625 / 16967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2861 : Bounds (16479617 / 200000000) (41199043 / 500000000) (Real.log (16967 / 15625)) := by
  have h := reflection_log_2861_neg
  have he : Real.log (16967 / 15625) = -Real.log (15625 / 16967) := by
    rw [show ((16967 / 15625) : ℝ) = ((15625 / 16967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2862_neg : (1403159 / 15625000) ≤ -Real.log (14283 / 15625) ∧
    -Real.log (14283 / 15625) ≤ (89802177 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 14954)) (n := 12)
    (lo := (1403159 / 15625000)) (hi := (89802177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14283) = 1/(14283 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2862 : Bounds (-89802177 / 1000000000) (-1403159 / 15625000) (Real.log (14283 / 15625)) := by
  have h := reflection_log_2862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2863_neg : (7404091 / 1000000000) ≤ -Real.log (242339661 / 244140625) ∧
    -Real.log (242339661 / 244140625) ≤ (1851023 / 250000000) := by
  have h := checkLog_sound (w := (900482 / 243240143)) (n := 12)
    (lo := (7404091 / 1000000000)) (hi := (1851023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242339661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242339661) = 1/(242339661 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2863 : Bounds (-1851023 / 250000000) (-7404091 / 1000000000) (Real.log (242339661 / 244140625)) := by
  have h := reflection_log_2863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2864_neg : (1841431 / 250000000) ≤ -Real.log (248165334111 / 250000000000) ∧
    -Real.log (248165334111 / 250000000000) ≤ (294629 / 40000000) := by
  have h := checkLog_sound (w := (1834665889 / 498165334111)) (n := 12)
    (lo := (1841431 / 250000000)) (hi := (294629 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248165334111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248165334111) = 1/(248165334111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2864 : Bounds (-294629 / 40000000) (-1841431 / 250000000) (Real.log (248165334111 / 250000000000)) := by
  have h := reflection_log_2864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2865_neg : (171752971 / 1000000000) ≤ -Real.log (250000000000 / 296846119689) ∧
    -Real.log (250000000000 / 296846119689) ≤ (42938243 / 250000000) := by
  have h := checkLog_sound (w := (46846119689 / 546846119689)) (n := 12)
    (lo := (171752971 / 1000000000)) (hi := (42938243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296846119689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296846119689 / 250000000000) = 1/(250000000000 / 296846119689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2865 : Bounds (171752971 / 1000000000) (42938243 / 250000000) (Real.log (296846119689 / 250000000000)) := by
  have h := reflection_log_2865_neg
  have he : Real.log (296846119689 / 250000000000) = -Real.log (250000000000 / 296846119689) := by
    rw [show ((296846119689 / 250000000000) : ℝ) = ((250000000000 / 296846119689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2866_neg : (86100131 / 500000000) ≤ -Real.log (62500000000 / 74244731499) ∧
    -Real.log (62500000000 / 74244731499) ≤ (172200263 / 1000000000) := by
  have h := checkLog_sound (w := (11744731499 / 136744731499)) (n := 12)
    (lo := (86100131 / 500000000)) (hi := (172200263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74244731499 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74244731499 / 62500000000) = 1/(62500000000 / 74244731499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2866 : Bounds (86100131 / 500000000) (172200263 / 1000000000) (Real.log (74244731499 / 62500000000)) := by
  have h := reflection_log_2866_neg
  have he : Real.log (74244731499 / 62500000000) = -Real.log (62500000000 / 74244731499) := by
    rw [show ((74244731499 / 62500000000) : ℝ) = ((62500000000 / 74244731499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2867_neg : (344569169 / 1000000000) ≤ -Real.log (500000000000 / 705690860863) ∧
    -Real.log (500000000000 / 705690860863) ≤ (34456917 / 100000000) := by
  have h := checkLog_sound (w := (205690860863 / 1205690860863)) (n := 12)
    (lo := (344569169 / 1000000000)) (hi := (34456917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705690860863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705690860863 / 500000000000) = 1/(500000000000 / 705690860863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2867 : Bounds (344569169 / 1000000000) (34456917 / 100000000) (Real.log (705690860863 / 500000000000)) := by
  have h := reflection_log_2867_neg
  have he : Real.log (705690860863 / 500000000000) = -Real.log (500000000000 / 705690860863) := by
    rw [show ((705690860863 / 500000000000) : ℝ) = ((500000000000 / 705690860863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2868_neg : (673389 / 1953125) ≤ -Real.log (250000000000 / 352918123719) ∧
    -Real.log (250000000000 / 352918123719) ≤ (344775169 / 1000000000) := by
  have h := checkLog_sound (w := (102918123719 / 602918123719)) (n := 12)
    (lo := (673389 / 1953125)) (hi := (344775169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352918123719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352918123719 / 250000000000) = 1/(250000000000 / 352918123719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2868 : Bounds (673389 / 1953125) (344775169 / 1000000000) (Real.log (352918123719 / 250000000000)) := by
  have h := reflection_log_2868_neg
  have he : Real.log (352918123719 / 250000000000) = -Real.log (250000000000 / 352918123719) := by
    rw [show ((352918123719 / 250000000000) : ℝ) = ((250000000000 / 352918123719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2869_neg : (6307491 / 40000000) ≤ -Real.log (2500 / 2927) ∧
    -Real.log (2500 / 2927) ≤ (39421819 / 250000000) := by
  have h := checkLog_sound (w := (427 / 5427)) (n := 12)
    (lo := (6307491 / 40000000)) (hi := (39421819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 2500) = 1/(2500 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2869 : Bounds (6307491 / 40000000) (39421819 / 250000000) (Real.log (2927 / 2500)) := by
  have h := reflection_log_2869_neg
  have he : Real.log (2927 / 2500) = -Real.log (2500 / 2927) := by
    rw [show ((2927 / 2500) : ℝ) = ((2500 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2870_neg : (93646949 / 500000000) ≤ -Real.log (2073 / 2500) ∧
    -Real.log (2073 / 2500) ≤ (187293899 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4573)) (n := 12)
    (lo := (93646949 / 500000000)) (hi := (187293899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2073) = 1/(2073 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2870 : Bounds (-187293899 / 1000000000) (-93646949 / 500000000) (Real.log (2073 / 2500)) := by
  have h := reflection_log_2870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2871_neg : (34157 / 200000000) ≤ -Real.log (2500000 / 2500427) ∧
    -Real.log (2500000 / 2500427) ≤ (85393 / 500000000) := by
  have h := checkLog_sound (w := (427 / 5000427)) (n := 12)
    (lo := (34157 / 200000000)) (hi := (85393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500427 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500427 / 2500000) = 1/(2500000 / 2500427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2871 : Bounds (34157 / 200000000) (85393 / 500000000) (Real.log (2500427 / 2500000)) := by
  have h := reflection_log_2871_neg
  have he : Real.log (2500427 / 2500000) = -Real.log (2500000 / 2500427) := by
    rw [show ((2500427 / 2500000) : ℝ) = ((2500000 / 2500427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2872_neg : (85407 / 500000000) ≤ -Real.log (2499573 / 2500000) ∧
    -Real.log (2499573 / 2500000) ≤ (34163 / 200000000) := by
  have h := checkLog_sound (w := (427 / 4999573)) (n := 12)
    (lo := (85407 / 500000000)) (hi := (34163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499573) = 1/(2499573 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2872 : Bounds (-34163 / 200000000) (-85407 / 500000000) (Real.log (2499573 / 2500000)) := by
  have h := reflection_log_2872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2873_neg : (41120299 / 500000000) ≤ -Real.log (1000000 / 1085717) ∧
    -Real.log (1000000 / 1085717) ≤ (82240599 / 1000000000) := by
  have h := checkLog_sound (w := (85717 / 2085717)) (n := 12)
    (lo := (41120299 / 500000000)) (hi := (82240599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085717 / 1000000) = 1/(1000000 / 1085717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2873 : Bounds (41120299 / 500000000) (82240599 / 1000000000) (Real.log (1085717 / 1000000)) := by
  have h := reflection_log_2873_neg
  have he : Real.log (1085717 / 1000000) = -Real.log (1000000 / 1085717) := by
    rw [show ((1085717 / 1000000) : ℝ) = ((1000000 / 1085717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2874_neg : (89615127 / 1000000000) ≤ -Real.log (914283 / 1000000) ∧
    -Real.log (914283 / 1000000) ≤ (11201891 / 125000000) := by
  have h := checkLog_sound (w := (85717 / 1914283)) (n := 12)
    (lo := (89615127 / 1000000000)) (hi := (11201891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914283) = 1/(914283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2874 : Bounds (-11201891 / 125000000) (-89615127 / 1000000000) (Real.log (914283 / 1000000)) := by
  have h := reflection_log_2874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2875_neg : (1648901 / 20000000) ≤ -Real.log (1000000 / 1085939) ∧
    -Real.log (1000000 / 1085939) ≤ (82445051 / 1000000000) := by
  have h := checkLog_sound (w := (85939 / 2085939)) (n := 12)
    (lo := (1648901 / 20000000)) (hi := (82445051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085939 / 1000000) = 1/(1000000 / 1085939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2875 : Bounds (1648901 / 20000000) (82445051 / 1000000000) (Real.log (1085939 / 1000000)) := by
  have h := reflection_log_2875_neg
  have he : Real.log (1085939 / 1000000) = -Real.log (1000000 / 1085939) := by
    rw [show ((1085939 / 1000000) : ℝ) = ((1000000 / 1085939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2876_neg : (8985797 / 100000000) ≤ -Real.log (914061 / 1000000) ∧
    -Real.log (914061 / 1000000) ≤ (89857971 / 1000000000) := by
  have h := checkLog_sound (w := (85939 / 1914061)) (n := 12)
    (lo := (8985797 / 100000000)) (hi := (89857971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914061) = 1/(914061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2876 : Bounds (-89857971 / 1000000000) (-8985797 / 100000000) (Real.log (914061 / 1000000)) := by
  have h := reflection_log_2876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2877_neg : (7412919 / 1000000000) ≤ -Real.log (992614488279 / 1000000000000) ∧
    -Real.log (992614488279 / 1000000000000) ≤ (185323 / 25000000) := by
  have h := checkLog_sound (w := (7385511721 / 1992614488279)) (n := 12)
    (lo := (7412919 / 1000000000)) (hi := (185323 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992614488279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992614488279) = 1/(992614488279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2877 : Bounds (-185323 / 25000000) (-7412919 / 1000000000) (Real.log (992614488279 / 1000000000000)) := by
  have h := reflection_log_2877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2878_neg : (7374529 / 1000000000) ≤ -Real.log (992652595911 / 1000000000000) ∧
    -Real.log (992652595911 / 1000000000000) ≤ (737453 / 100000000) := by
  have h := checkLog_sound (w := (7347404089 / 1992652595911)) (n := 12)
    (lo := (7374529 / 1000000000)) (hi := (737453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992652595911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992652595911) = 1/(992652595911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2878 : Bounds (-737453 / 100000000) (-7374529 / 1000000000) (Real.log (992652595911 / 1000000000000)) := by
  have h := reflection_log_2878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2879_neg : (6874229 / 40000000) ≤ -Real.log (500000000000 / 593753247079) ∧
    -Real.log (500000000000 / 593753247079) ≤ (85927863 / 500000000) := by
  have h := checkLog_sound (w := (93753247079 / 1093753247079)) (n := 12)
    (lo := (6874229 / 40000000)) (hi := (85927863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593753247079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593753247079 / 500000000000) = 1/(500000000000 / 593753247079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2879 : Bounds (6874229 / 40000000) (85927863 / 500000000) (Real.log (593753247079 / 500000000000)) := by
  have h := reflection_log_2879_neg
  have he : Real.log (593753247079 / 500000000000) = -Real.log (500000000000 / 593753247079) := by
    rw [show ((593753247079 / 500000000000) : ℝ) = ((500000000000 / 593753247079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0045 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2880_neg : (8615151 / 50000000) ≤ -Real.log (500000000000 / 594018889331) ∧
    -Real.log (500000000000 / 594018889331) ≤ (172303021 / 1000000000) := by
  have h := checkLog_sound (w := (94018889331 / 1094018889331)) (n := 12)
    (lo := (8615151 / 50000000)) (hi := (172303021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594018889331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594018889331 / 500000000000) = 1/(500000000000 / 594018889331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2880 : Bounds (8615151 / 50000000) (172303021 / 1000000000) (Real.log (594018889331 / 500000000000)) := by
  have h := reflection_log_2880_neg
  have he : Real.log (594018889331 / 500000000000) = -Real.log (500000000000 / 594018889331) := by
    rw [show ((594018889331 / 500000000000) : ℝ) = ((500000000000 / 594018889331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2881_neg : (673389 / 1953125) ≤ -Real.log (500000000000 / 705836247437) ∧
    -Real.log (500000000000 / 705836247437) ≤ (344775169 / 1000000000) := by
  have h := checkLog_sound (w := (205836247437 / 1205836247437)) (n := 12)
    (lo := (673389 / 1953125)) (hi := (344775169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705836247437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705836247437 / 500000000000) = 1/(500000000000 / 705836247437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2881 : Bounds (673389 / 1953125) (344775169 / 1000000000) (Real.log (705836247437 / 500000000000)) := by
  have h := reflection_log_2881_neg
  have he : Real.log (705836247437 / 500000000000) = -Real.log (500000000000 / 705836247437) := by
    rw [show ((705836247437 / 500000000000) : ℝ) = ((500000000000 / 705836247437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2882_neg : (172490587 / 500000000) ≤ -Real.log (500000000000 / 705981669079) ∧
    -Real.log (500000000000 / 705981669079) ≤ (13799247 / 40000000) := by
  have h := checkLog_sound (w := (205981669079 / 1205981669079)) (n := 12)
    (lo := (172490587 / 500000000)) (hi := (13799247 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705981669079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705981669079 / 500000000000) = 1/(500000000000 / 705981669079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2882 : Bounds (172490587 / 500000000) (13799247 / 40000000) (Real.log (705981669079 / 500000000000)) := by
  have h := reflection_log_2882_neg
  have he : Real.log (705981669079 / 500000000000) = -Real.log (500000000000 / 705981669079) := by
    rw [show ((705981669079 / 500000000000) : ℝ) = ((500000000000 / 705981669079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2883_neg : (157772683 / 1000000000) ≤ -Real.log (10000 / 11709) ∧
    -Real.log (10000 / 11709) ≤ (39443171 / 250000000) := by
  have h := checkLog_sound (w := (1709 / 21709)) (n := 12)
    (lo := (157772683 / 1000000000)) (hi := (39443171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11709 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11709 / 10000) = 1/(10000 / 11709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2883 : Bounds (157772683 / 1000000000) (39443171 / 250000000) (Real.log (11709 / 10000)) := by
  have h := reflection_log_2883_neg
  have he : Real.log (11709 / 10000) = -Real.log (10000 / 11709) := by
    rw [show ((11709 / 10000) : ℝ) = ((10000 / 11709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2884_neg : (187414503 / 1000000000) ≤ -Real.log (8291 / 10000) ∧
    -Real.log (8291 / 10000) ≤ (23426813 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 18291)) (n := 12)
    (lo := (187414503 / 1000000000)) (hi := (23426813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8291) = 1/(8291 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2884 : Bounds (-23426813 / 125000000) (-187414503 / 1000000000) (Real.log (8291 / 10000)) := by
  have h := reflection_log_2884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2885_neg : (34177 / 200000000) ≤ -Real.log (10000000 / 10001709) ∧
    -Real.log (10000000 / 10001709) ≤ (85443 / 500000000) := by
  have h := checkLog_sound (w := (1709 / 20001709)) (n := 12)
    (lo := (34177 / 200000000)) (hi := (85443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001709 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001709 / 10000000) = 1/(10000000 / 10001709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2885 : Bounds (34177 / 200000000) (85443 / 500000000) (Real.log (10001709 / 10000000)) := by
  have h := reflection_log_2885_neg
  have he : Real.log (10001709 / 10000000) = -Real.log (10000000 / 10001709) := by
    rw [show ((10001709 / 10000000) : ℝ) = ((10000000 / 10001709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2886_neg : (85457 / 500000000) ≤ -Real.log (9998291 / 10000000) ∧
    -Real.log (9998291 / 10000000) ≤ (34183 / 200000000) := by
  have h := checkLog_sound (w := (1709 / 19998291)) (n := 12)
    (lo := (85457 / 500000000)) (hi := (34183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998291) = 1/(9998291 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2886 : Bounds (-34183 / 200000000) (-85457 / 500000000) (Real.log (9998291 / 10000000)) := by
  have h := reflection_log_2886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2887_neg : (8228757 / 100000000) ≤ -Real.log (125000 / 135721) ∧
    -Real.log (125000 / 135721) ≤ (82287571 / 1000000000) := by
  have h := checkLog_sound (w := (10721 / 260721)) (n := 12)
    (lo := (8228757 / 100000000)) (hi := (82287571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135721 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135721 / 125000) = 1/(125000 / 135721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2887 : Bounds (8228757 / 100000000) (82287571 / 1000000000) (Real.log (135721 / 125000)) := by
  have h := reflection_log_2887_neg
  have he : Real.log (135721 / 125000) = -Real.log (125000 / 135721) := by
    rw [show ((135721 / 125000) : ℝ) = ((125000 / 135721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2888_neg : (8967091 / 100000000) ≤ -Real.log (114279 / 125000) ∧
    -Real.log (114279 / 125000) ≤ (89670911 / 1000000000) := by
  have h := checkLog_sound (w := (10721 / 239279)) (n := 12)
    (lo := (8967091 / 100000000)) (hi := (89670911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114279) = 1/(114279 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2888 : Bounds (-89670911 / 1000000000) (-8967091 / 100000000) (Real.log (114279 / 125000)) := by
  have h := reflection_log_2888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2889_neg : (20622773 / 250000000) ≤ -Real.log (1000000 / 1085989) ∧
    -Real.log (1000000 / 1085989) ≤ (82491093 / 1000000000) := by
  have h := checkLog_sound (w := (85989 / 2085989)) (n := 12)
    (lo := (20622773 / 250000000)) (hi := (82491093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085989 / 1000000) = 1/(1000000 / 1085989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2889 : Bounds (20622773 / 250000000) (82491093 / 1000000000) (Real.log (1085989 / 1000000)) := by
  have h := reflection_log_2889_neg
  have he : Real.log (1085989 / 1000000) = -Real.log (1000000 / 1085989) := by
    rw [show ((1085989 / 1000000) : ℝ) = ((1000000 / 1085989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2890_neg : (2809771 / 31250000) ≤ -Real.log (914011 / 1000000) ∧
    -Real.log (914011 / 1000000) ≤ (89912673 / 1000000000) := by
  have h := checkLog_sound (w := (85989 / 1914011)) (n := 12)
    (lo := (2809771 / 31250000)) (hi := (89912673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914011) = 1/(914011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2890 : Bounds (-89912673 / 1000000000) (-2809771 / 31250000) (Real.log (914011 / 1000000)) := by
  have h := reflection_log_2890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2891_neg : (371079 / 50000000) ≤ -Real.log (992605891879 / 1000000000000) ∧
    -Real.log (992605891879 / 1000000000000) ≤ (7421581 / 1000000000) := by
  have h := checkLog_sound (w := (7394108121 / 1992605891879)) (n := 12)
    (lo := (371079 / 50000000)) (hi := (7421581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992605891879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992605891879) = 1/(992605891879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2891 : Bounds (-7421581 / 1000000000) (-371079 / 50000000) (Real.log (992605891879 / 1000000000000)) := by
  have h := reflection_log_2891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2892_neg : (7383339 / 1000000000) ≤ -Real.log (15510060159 / 15625000000) ∧
    -Real.log (15510060159 / 15625000000) ≤ (369167 / 50000000) := by
  have h := checkLog_sound (w := (114939841 / 31135060159)) (n := 12)
    (lo := (7383339 / 1000000000)) (hi := (369167 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15510060159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15510060159) = 1/(15510060159 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2892 : Bounds (-369167 / 50000000) (-7383339 / 1000000000) (Real.log (15510060159 / 15625000000)) := by
  have h := reflection_log_2892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2893_neg : (171958481 / 1000000000) ≤ -Real.log (500000000000 / 593814261587) ∧
    -Real.log (500000000000 / 593814261587) ≤ (85979241 / 500000000) := by
  have h := checkLog_sound (w := (93814261587 / 1093814261587)) (n := 12)
    (lo := (171958481 / 1000000000)) (hi := (85979241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593814261587 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593814261587 / 500000000000) = 1/(500000000000 / 593814261587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2893 : Bounds (171958481 / 1000000000) (85979241 / 500000000) (Real.log (593814261587 / 500000000000)) := by
  have h := reflection_log_2893_neg
  have he : Real.log (593814261587 / 500000000000) = -Real.log (500000000000 / 593814261587) := by
    rw [show ((593814261587 / 500000000000) : ℝ) = ((500000000000 / 593814261587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2894_neg : (34480753 / 200000000) ≤ -Real.log (500000000000 / 594078736471) ∧
    -Real.log (500000000000 / 594078736471) ≤ (86201883 / 500000000) := by
  have h := checkLog_sound (w := (94078736471 / 1094078736471)) (n := 12)
    (lo := (34480753 / 200000000)) (hi := (86201883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594078736471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594078736471 / 500000000000) = 1/(500000000000 / 594078736471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2894 : Bounds (34480753 / 200000000) (86201883 / 500000000) (Real.log (594078736471 / 500000000000)) := by
  have h := reflection_log_2894_neg
  have he : Real.log (594078736471 / 500000000000) = -Real.log (500000000000 / 594078736471) := by
    rw [show ((594078736471 / 500000000000) : ℝ) = ((500000000000 / 594078736471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2895_neg : (172490587 / 500000000) ≤ -Real.log (250000000000 / 352990834539) ∧
    -Real.log (250000000000 / 352990834539) ≤ (13799247 / 40000000) := by
  have h := checkLog_sound (w := (102990834539 / 602990834539)) (n := 12)
    (lo := (172490587 / 500000000)) (hi := (13799247 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352990834539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352990834539 / 250000000000) = 1/(250000000000 / 352990834539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2895 : Bounds (172490587 / 500000000) (13799247 / 40000000) (Real.log (352990834539 / 250000000000)) := by
  have h := reflection_log_2895_neg
  have he : Real.log (352990834539 / 250000000000) = -Real.log (250000000000 / 352990834539) := by
    rw [show ((352990834539 / 250000000000) : ℝ) = ((250000000000 / 352990834539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2896_neg : (345187187 / 1000000000) ≤ -Real.log (2500000000 / 3530635629) ∧
    -Real.log (2500000000 / 3530635629) ≤ (86296797 / 250000000) := by
  have h := checkLog_sound (w := (1030635629 / 6030635629)) (n := 12)
    (lo := (345187187 / 1000000000)) (hi := (86296797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3530635629 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3530635629 / 2500000000) = 1/(2500000000 / 3530635629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2896 : Bounds (345187187 / 1000000000) (86296797 / 250000000) (Real.log (3530635629 / 2500000000)) := by
  have h := reflection_log_2896_neg
  have he : Real.log (3530635629 / 2500000000) = -Real.log (2500000000 / 3530635629) := by
    rw [show ((3530635629 / 2500000000) : ℝ) = ((2500000000 / 3530635629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2897_neg : (39464521 / 250000000) ≤ -Real.log (1000 / 1171) ∧
    -Real.log (1000 / 1171) ≤ (31571617 / 200000000) := by
  have h := checkLog_sound (w := (171 / 2171)) (n := 12)
    (lo := (39464521 / 250000000)) (hi := (31571617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171 / 1000) = 1/(1000 / 1171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2897 : Bounds (39464521 / 250000000) (31571617 / 200000000) (Real.log (1171 / 1000)) := by
  have h := reflection_log_2897_neg
  have he : Real.log (1171 / 1000) = -Real.log (1000 / 1171) := by
    rw [show ((1171 / 1000) : ℝ) = ((1000 / 1171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2898_neg : (187535123 / 1000000000) ≤ -Real.log (829 / 1000) ∧
    -Real.log (829 / 1000) ≤ (46883781 / 250000000) := by
  have h := checkLog_sound (w := (171 / 1829)) (n := 12)
    (lo := (187535123 / 1000000000)) (hi := (46883781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 829) = 1/(829 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2898 : Bounds (-46883781 / 250000000) (-187535123 / 1000000000) (Real.log (829 / 1000)) := by
  have h := reflection_log_2898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2899_neg : (34197 / 200000000) ≤ -Real.log (1000000 / 1000171) ∧
    -Real.log (1000000 / 1000171) ≤ (85493 / 500000000) := by
  have h := checkLog_sound (w := (171 / 2000171)) (n := 12)
    (lo := (34197 / 200000000)) (hi := (85493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000171 / 1000000) = 1/(1000000 / 1000171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2899 : Bounds (34197 / 200000000) (85493 / 500000000) (Real.log (1000171 / 1000000)) := by
  have h := reflection_log_2899_neg
  have he : Real.log (1000171 / 1000000) = -Real.log (1000000 / 1000171) := by
    rw [show ((1000171 / 1000000) : ℝ) = ((1000000 / 1000171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2900_neg : (85507 / 500000000) ≤ -Real.log (999829 / 1000000) ∧
    -Real.log (999829 / 1000000) ≤ (34203 / 200000000) := by
  have h := checkLog_sound (w := (171 / 1999829)) (n := 12)
    (lo := (85507 / 500000000)) (hi := (34203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999829) = 1/(999829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2900 : Bounds (-34203 / 200000000) (-85507 / 500000000) (Real.log (999829 / 1000000)) := by
  have h := reflection_log_2900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2901_neg : (82333619 / 1000000000) ≤ -Real.log (500000 / 542909) ∧
    -Real.log (500000 / 542909) ≤ (4116681 / 50000000) := by
  have h := checkLog_sound (w := (42909 / 1042909)) (n := 12)
    (lo := (82333619 / 1000000000)) (hi := (4116681 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542909 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542909 / 500000) = 1/(500000 / 542909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2901 : Bounds (82333619 / 1000000000) (4116681 / 50000000) (Real.log (542909 / 500000)) := by
  have h := reflection_log_2901_neg
  have he : Real.log (542909 / 500000) = -Real.log (500000 / 542909) := by
    rw [show ((542909 / 500000) : ℝ) = ((500000 / 542909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2902_neg : (44862801 / 500000000) ≤ -Real.log (457091 / 500000) ∧
    -Real.log (457091 / 500000) ≤ (89725603 / 1000000000) := by
  have h := checkLog_sound (w := (42909 / 957091)) (n := 12)
    (lo := (44862801 / 500000000)) (hi := (89725603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457091) = 1/(457091 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2902 : Bounds (-89725603 / 1000000000) (-44862801 / 500000000) (Real.log (457091 / 500000)) := by
  have h := reflection_log_2902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2903_neg : (82538053 / 1000000000) ≤ -Real.log (25000 / 27151) ∧
    -Real.log (25000 / 27151) ≤ (41269027 / 500000000) := by
  have h := checkLog_sound (w := (2151 / 52151)) (n := 12)
    (lo := (82538053 / 1000000000)) (hi := (41269027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27151 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27151 / 25000) = 1/(25000 / 27151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2903 : Bounds (82538053 / 1000000000) (41269027 / 500000000) (Real.log (27151 / 25000)) := by
  have h := reflection_log_2903_neg
  have he : Real.log (27151 / 25000) = -Real.log (25000 / 27151) := by
    rw [show ((27151 / 25000) : ℝ) = ((25000 / 27151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2904_neg : (11246059 / 125000000) ≤ -Real.log (22849 / 25000) ∧
    -Real.log (22849 / 25000) ≤ (89968473 / 1000000000) := by
  have h := checkLog_sound (w := (2151 / 47849)) (n := 12)
    (lo := (11246059 / 125000000)) (hi := (89968473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22849) = 1/(22849 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2904 : Bounds (-89968473 / 1000000000) (-11246059 / 125000000) (Real.log (22849 / 25000)) := by
  have h := reflection_log_2904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2905_neg : (3715209 / 500000000) ≤ -Real.log (620373199 / 625000000) ∧
    -Real.log (620373199 / 625000000) ≤ (7430419 / 1000000000) := by
  have h := checkLog_sound (w := (4626801 / 1245373199)) (n := 12)
    (lo := (3715209 / 500000000)) (hi := (7430419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620373199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620373199) = 1/(620373199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2905 : Bounds (-7430419 / 1000000000) (-3715209 / 500000000) (Real.log (620373199 / 625000000)) := by
  have h := reflection_log_2905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2906_neg : (3695991 / 500000000) ≤ -Real.log (248158817719 / 250000000000) ∧
    -Real.log (248158817719 / 250000000000) ≤ (7391983 / 1000000000) := by
  have h := checkLog_sound (w := (1841182281 / 498158817719)) (n := 12)
    (lo := (3695991 / 500000000)) (hi := (7391983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248158817719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248158817719) = 1/(248158817719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2906 : Bounds (-7391983 / 1000000000) (-3695991 / 500000000) (Real.log (248158817719 / 250000000000)) := by
  have h := reflection_log_2906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2907_neg : (86029611 / 500000000) ≤ -Real.log (500000000000 / 593874086341) ∧
    -Real.log (500000000000 / 593874086341) ≤ (172059223 / 1000000000) := by
  have h := checkLog_sound (w := (93874086341 / 1093874086341)) (n := 12)
    (lo := (86029611 / 500000000)) (hi := (172059223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593874086341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593874086341 / 500000000000) = 1/(500000000000 / 593874086341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2907 : Bounds (86029611 / 500000000) (172059223 / 1000000000) (Real.log (593874086341 / 500000000000)) := by
  have h := reflection_log_2907_neg
  have he : Real.log (593874086341 / 500000000000) = -Real.log (500000000000 / 593874086341) := by
    rw [show ((593874086341 / 500000000000) : ℝ) = ((500000000000 / 593874086341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2908_neg : (6900261 / 40000000) ≤ -Real.log (5000000000 / 5941397873) ∧
    -Real.log (5000000000 / 5941397873) ≤ (86253263 / 500000000) := by
  have h := checkLog_sound (w := (941397873 / 10941397873)) (n := 12)
    (lo := (6900261 / 40000000)) (hi := (86253263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5941397873 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5941397873 / 5000000000) = 1/(5000000000 / 5941397873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2908 : Bounds (6900261 / 40000000) (86253263 / 500000000) (Real.log (5941397873 / 5000000000)) := by
  have h := reflection_log_2908_neg
  have he : Real.log (5941397873 / 5000000000) = -Real.log (5000000000 / 5941397873) := by
    rw [show ((5941397873 / 5000000000) : ℝ) = ((5000000000 / 5941397873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2909_neg : (345187187 / 1000000000) ≤ -Real.log (500000000000 / 706127125799) ∧
    -Real.log (500000000000 / 706127125799) ≤ (86296797 / 250000000) := by
  have h := checkLog_sound (w := (206127125799 / 1206127125799)) (n := 12)
    (lo := (345187187 / 1000000000)) (hi := (86296797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706127125799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706127125799 / 500000000000) = 1/(500000000000 / 706127125799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2909 : Bounds (345187187 / 1000000000) (86296797 / 250000000) (Real.log (706127125799 / 500000000000)) := by
  have h := reflection_log_2909_neg
  have he : Real.log (706127125799 / 500000000000) = -Real.log (500000000000 / 706127125799) := by
    rw [show ((706127125799 / 500000000000) : ℝ) = ((500000000000 / 706127125799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2910_neg : (43174151 / 125000000) ≤ -Real.log (125000000000 / 176568154403) ∧
    -Real.log (125000000000 / 176568154403) ≤ (345393209 / 1000000000) := by
  have h := checkLog_sound (w := (51568154403 / 301568154403)) (n := 12)
    (lo := (43174151 / 125000000)) (hi := (345393209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176568154403 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176568154403 / 125000000000) = 1/(125000000000 / 176568154403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2910 : Bounds (43174151 / 125000000) (345393209 / 1000000000) (Real.log (176568154403 / 125000000000)) := by
  have h := reflection_log_2910_neg
  have he : Real.log (176568154403 / 125000000000) = -Real.log (125000000000 / 176568154403) := by
    rw [show ((176568154403 / 125000000000) : ℝ) = ((125000000000 / 176568154403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2911_neg : (78971739 / 500000000) ≤ -Real.log (10000 / 11711) ∧
    -Real.log (10000 / 11711) ≤ (157943479 / 1000000000) := by
  have h := checkLog_sound (w := (1711 / 21711)) (n := 12)
    (lo := (78971739 / 500000000)) (hi := (157943479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11711 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11711 / 10000) = 1/(10000 / 11711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2911 : Bounds (78971739 / 500000000) (157943479 / 1000000000) (Real.log (11711 / 10000)) := by
  have h := reflection_log_2911_neg
  have he : Real.log (11711 / 10000) = -Real.log (10000 / 11711) := by
    rw [show ((11711 / 10000) : ℝ) = ((10000 / 11711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2912_neg : (93827879 / 500000000) ≤ -Real.log (8289 / 10000) ∧
    -Real.log (8289 / 10000) ≤ (187655759 / 1000000000) := by
  have h := checkLog_sound (w := (1711 / 18289)) (n := 12)
    (lo := (93827879 / 500000000)) (hi := (187655759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8289) = 1/(8289 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2912 : Bounds (-187655759 / 1000000000) (-93827879 / 500000000) (Real.log (8289 / 10000)) := by
  have h := reflection_log_2912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2913_neg : (34217 / 200000000) ≤ -Real.log (10000000 / 10001711) ∧
    -Real.log (10000000 / 10001711) ≤ (85543 / 500000000) := by
  have h := checkLog_sound (w := (1711 / 20001711)) (n := 12)
    (lo := (34217 / 200000000)) (hi := (85543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001711 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001711 / 10000000) = 1/(10000000 / 10001711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2913 : Bounds (34217 / 200000000) (85543 / 500000000) (Real.log (10001711 / 10000000)) := by
  have h := reflection_log_2913_neg
  have he : Real.log (10001711 / 10000000) = -Real.log (10000000 / 10001711) := by
    rw [show ((10001711 / 10000000) : ℝ) = ((10000000 / 10001711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2914_neg : (85557 / 500000000) ≤ -Real.log (9998289 / 10000000) ∧
    -Real.log (9998289 / 10000000) ≤ (34223 / 200000000) := by
  have h := checkLog_sound (w := (1711 / 19998289)) (n := 12)
    (lo := (85557 / 500000000)) (hi := (34223 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998289) = 1/(9998289 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2914 : Bounds (-34223 / 200000000) (-85557 / 500000000) (Real.log (9998289 / 10000000)) := by
  have h := reflection_log_2914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2915_neg : (20595147 / 250000000) ≤ -Real.log (1000000 / 1085869) ∧
    -Real.log (1000000 / 1085869) ≤ (82380589 / 1000000000) := by
  have h := checkLog_sound (w := (85869 / 2085869)) (n := 12)
    (lo := (20595147 / 250000000)) (hi := (82380589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085869 / 1000000) = 1/(1000000 / 1085869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2915 : Bounds (20595147 / 250000000) (82380589 / 1000000000) (Real.log (1085869 / 1000000)) := by
  have h := reflection_log_2915_neg
  have he : Real.log (1085869 / 1000000) = -Real.log (1000000 / 1085869) := by
    rw [show ((1085869 / 1000000) : ℝ) = ((1000000 / 1085869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2916_neg : (89781391 / 1000000000) ≤ -Real.log (914131 / 1000000) ∧
    -Real.log (914131 / 1000000) ≤ (5611337 / 62500000) := by
  have h := checkLog_sound (w := (85869 / 1914131)) (n := 12)
    (lo := (89781391 / 1000000000)) (hi := (5611337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914131) = 1/(914131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2916 : Bounds (-5611337 / 62500000) (-89781391 / 1000000000) (Real.log (914131 / 1000000)) := by
  have h := reflection_log_2916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2917_neg : (82585011 / 1000000000) ≤ -Real.log (1000000 / 1086091) ∧
    -Real.log (1000000 / 1086091) ≤ (20646253 / 250000000) := by
  have h := checkLog_sound (w := (86091 / 2086091)) (n := 12)
    (lo := (82585011 / 1000000000)) (hi := (20646253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086091 / 1000000) = 1/(1000000 / 1086091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2917 : Bounds (82585011 / 1000000000) (20646253 / 250000000) (Real.log (1086091 / 1000000)) := by
  have h := reflection_log_2917_neg
  have he : Real.log (1086091 / 1000000) = -Real.log (1000000 / 1086091) := by
    rw [show ((1086091 / 1000000) : ℝ) = ((1000000 / 1086091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2918_neg : (45012137 / 500000000) ≤ -Real.log (913909 / 1000000) ∧
    -Real.log (913909 / 1000000) ≤ (3600971 / 40000000) := by
  have h := checkLog_sound (w := (86091 / 1913909)) (n := 12)
    (lo := (45012137 / 500000000)) (hi := (3600971 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913909) = 1/(913909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2918 : Bounds (-3600971 / 40000000) (-45012137 / 500000000) (Real.log (913909 / 1000000)) := by
  have h := reflection_log_2918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2919_neg : (7439263 / 1000000000) ≤ -Real.log (992588339719 / 1000000000000) ∧
    -Real.log (992588339719 / 1000000000000) ≤ (232477 / 31250000) := by
  have h := checkLog_sound (w := (7411660281 / 1992588339719)) (n := 12)
    (lo := (7439263 / 1000000000)) (hi := (232477 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992588339719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992588339719) = 1/(992588339719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2919 : Bounds (-232477 / 31250000) (-7439263 / 1000000000) (Real.log (992588339719 / 1000000000000)) := by
  have h := reflection_log_2919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2920_neg : (7400803 / 1000000000) ≤ -Real.log (992626514839 / 1000000000000) ∧
    -Real.log (992626514839 / 1000000000000) ≤ (1850201 / 250000000) := by
  have h := checkLog_sound (w := (7373485161 / 1992626514839)) (n := 12)
    (lo := (7400803 / 1000000000)) (hi := (1850201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992626514839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992626514839) = 1/(992626514839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2920 : Bounds (-1850201 / 250000000) (-7400803 / 1000000000) (Real.log (992626514839 / 1000000000000)) := by
  have h := reflection_log_2920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2921_neg : (172161979 / 1000000000) ≤ -Real.log (125000000000 / 148483778583) ∧
    -Real.log (125000000000 / 148483778583) ≤ (8608099 / 50000000) := by
  have h := checkLog_sound (w := (23483778583 / 273483778583)) (n := 12)
    (lo := (172161979 / 1000000000)) (hi := (8608099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148483778583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148483778583 / 125000000000) = 1/(125000000000 / 148483778583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2921 : Bounds (172161979 / 1000000000) (8608099 / 50000000) (Real.log (148483778583 / 125000000000)) := by
  have h := reflection_log_2921_neg
  have he : Real.log (148483778583 / 125000000000) = -Real.log (125000000000 / 148483778583) := by
    rw [show ((148483778583 / 125000000000) : ℝ) = ((125000000000 / 148483778583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2922_neg : (86304643 / 500000000) ≤ -Real.log (250000000000 / 297100422471) ∧
    -Real.log (250000000000 / 297100422471) ≤ (172609287 / 1000000000) := by
  have h := checkLog_sound (w := (47100422471 / 547100422471)) (n := 12)
    (lo := (86304643 / 500000000)) (hi := (172609287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297100422471 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297100422471 / 250000000000) = 1/(250000000000 / 297100422471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2922 : Bounds (86304643 / 500000000) (172609287 / 1000000000) (Real.log (297100422471 / 250000000000)) := by
  have h := reflection_log_2922_neg
  have he : Real.log (297100422471 / 250000000000) = -Real.log (250000000000 / 297100422471) := by
    rw [show ((297100422471 / 250000000000) : ℝ) = ((250000000000 / 297100422471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2923_neg : (43174151 / 125000000) ≤ -Real.log (500000000000 / 706272617611) ∧
    -Real.log (500000000000 / 706272617611) ≤ (345393209 / 1000000000) := by
  have h := checkLog_sound (w := (206272617611 / 1206272617611)) (n := 12)
    (lo := (43174151 / 125000000)) (hi := (345393209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706272617611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706272617611 / 500000000000) = 1/(500000000000 / 706272617611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2923 : Bounds (43174151 / 125000000) (345393209 / 1000000000) (Real.log (706272617611 / 500000000000)) := by
  have h := reflection_log_2923_neg
  have he : Real.log (706272617611 / 500000000000) = -Real.log (500000000000 / 706272617611) := by
    rw [show ((706272617611 / 500000000000) : ℝ) = ((500000000000 / 706272617611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2924_neg : (86399809 / 250000000) ≤ -Real.log (500000000000 / 706418144529) ∧
    -Real.log (500000000000 / 706418144529) ≤ (345599237 / 1000000000) := by
  have h := checkLog_sound (w := (206418144529 / 1206418144529)) (n := 12)
    (lo := (86399809 / 250000000)) (hi := (345599237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706418144529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706418144529 / 500000000000) = 1/(500000000000 / 706418144529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2924 : Bounds (86399809 / 250000000) (345599237 / 1000000000) (Real.log (706418144529 / 500000000000)) := by
  have h := reflection_log_2924_neg
  have he : Real.log (706418144529 / 500000000000) = -Real.log (500000000000 / 706418144529) := by
    rw [show ((706418144529 / 500000000000) : ℝ) = ((500000000000 / 706418144529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2925_neg : (2469201 / 15625000) ≤ -Real.log (625 / 732) ∧
    -Real.log (625 / 732) ≤ (31605773 / 200000000) := by
  have h := checkLog_sound (w := (107 / 1357)) (n := 12)
    (lo := (2469201 / 15625000)) (hi := (31605773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732 / 625) = 1/(625 / 732) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2925 : Bounds (2469201 / 15625000) (31605773 / 200000000) (Real.log (732 / 625)) := by
  have h := reflection_log_2925_neg
  have he : Real.log (732 / 625) = -Real.log (625 / 732) := by
    rw [show ((732 / 625) : ℝ) = ((625 / 732) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2926_neg : (187776407 / 1000000000) ≤ -Real.log (518 / 625) ∧
    -Real.log (518 / 625) ≤ (23472051 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1143)) (n := 12)
    (lo := (187776407 / 1000000000)) (hi := (23472051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 518) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 518) = 1/(518 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2926 : Bounds (-23472051 / 125000000) (-187776407 / 1000000000) (Real.log (518 / 625)) := by
  have h := reflection_log_2926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2927_neg : (34237 / 200000000) ≤ -Real.log (625000 / 625107) ∧
    -Real.log (625000 / 625107) ≤ (85593 / 500000000) := by
  have h := checkLog_sound (w := (107 / 1250107)) (n := 12)
    (lo := (34237 / 200000000)) (hi := (85593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625107 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625107 / 625000) = 1/(625000 / 625107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2927 : Bounds (34237 / 200000000) (85593 / 500000000) (Real.log (625107 / 625000)) := by
  have h := reflection_log_2927_neg
  have he : Real.log (625107 / 625000) = -Real.log (625000 / 625107) := by
    rw [show ((625107 / 625000) : ℝ) = ((625000 / 625107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2928_neg : (85607 / 500000000) ≤ -Real.log (624893 / 625000) ∧
    -Real.log (624893 / 625000) ≤ (34243 / 200000000) := by
  have h := checkLog_sound (w := (107 / 1249893)) (n := 12)
    (lo := (85607 / 500000000)) (hi := (34243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624893) = 1/(624893 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2928 : Bounds (-34243 / 200000000) (-85607 / 500000000) (Real.log (624893 / 625000)) := by
  have h := reflection_log_2928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2929_neg : (82427553 / 1000000000) ≤ -Real.log (6250 / 6787) ∧
    -Real.log (6250 / 6787) ≤ (41213777 / 500000000) := by
  have h := checkLog_sound (w := (537 / 13037)) (n := 12)
    (lo := (82427553 / 1000000000)) (hi := (41213777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 6250) = 1/(6250 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2929 : Bounds (82427553 / 1000000000) (41213777 / 500000000) (Real.log (6787 / 6250)) := by
  have h := reflection_log_2929_neg
  have he : Real.log (6787 / 6250) = -Real.log (6250 / 6787) := by
    rw [show ((6787 / 6250) : ℝ) = ((6250 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2930_neg : (701853 / 7812500) ≤ -Real.log (5713 / 6250) ∧
    -Real.log (5713 / 6250) ≤ (17967437 / 200000000) := by
  have h := checkLog_sound (w := (537 / 11963)) (n := 12)
    (lo := (701853 / 7812500)) (hi := (17967437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5713) = 1/(5713 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2930 : Bounds (-17967437 / 200000000) (-701853 / 7812500) (Real.log (5713 / 6250)) := by
  have h := reflection_log_2930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2931_neg : (2582249 / 31250000) ≤ -Real.log (500000 / 543071) ∧
    -Real.log (500000 / 543071) ≤ (82631969 / 1000000000) := by
  have h := checkLog_sound (w := (43071 / 1043071)) (n := 12)
    (lo := (2582249 / 31250000)) (hi := (82631969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543071 / 500000) = 1/(500000 / 543071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2931 : Bounds (2582249 / 31250000) (82631969 / 1000000000) (Real.log (543071 / 500000)) := by
  have h := reflection_log_2931_neg
  have he : Real.log (543071 / 500000) = -Real.log (500000 / 543071) := by
    rw [show ((543071 / 500000) : ℝ) = ((500000 / 543071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2932_neg : (1126001 / 12500000) ≤ -Real.log (456929 / 500000) ∧
    -Real.log (456929 / 500000) ≤ (90080081 / 1000000000) := by
  have h := checkLog_sound (w := (43071 / 956929)) (n := 12)
    (lo := (1126001 / 12500000)) (hi := (90080081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456929) = 1/(456929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2932 : Bounds (-90080081 / 1000000000) (-1126001 / 12500000) (Real.log (456929 / 500000)) := by
  have h := reflection_log_2932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2933_neg : (465507 / 62500000) ≤ -Real.log (248144888959 / 250000000000) ∧
    -Real.log (248144888959 / 250000000000) ≤ (7448113 / 1000000000) := by
  have h := checkLog_sound (w := (1855111041 / 498144888959)) (n := 12)
    (lo := (465507 / 62500000)) (hi := (7448113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248144888959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248144888959) = 1/(248144888959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2933 : Bounds (-7448113 / 1000000000) (-465507 / 62500000) (Real.log (248144888959 / 250000000000)) := by
  have h := reflection_log_2933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2934_neg : (740963 / 100000000) ≤ -Real.log (38774131 / 39062500) ∧
    -Real.log (38774131 / 39062500) ≤ (7409631 / 1000000000) := by
  have h := checkLog_sound (w := (288369 / 77836631)) (n := 12)
    (lo := (740963 / 100000000)) (hi := (7409631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38774131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38774131) = 1/(38774131 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2934 : Bounds (-7409631 / 1000000000) (-740963 / 100000000) (Real.log (38774131 / 39062500)) := by
  have h := reflection_log_2934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2935_neg : (172264737 / 1000000000) ≤ -Real.log (500000000000 / 593996149133) ∧
    -Real.log (500000000000 / 593996149133) ≤ (86132369 / 500000000) := by
  have h := checkLog_sound (w := (93996149133 / 1093996149133)) (n := 12)
    (lo := (172264737 / 1000000000)) (hi := (86132369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593996149133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593996149133 / 500000000000) = 1/(500000000000 / 593996149133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2935 : Bounds (172264737 / 1000000000) (86132369 / 500000000) (Real.log (593996149133 / 500000000000)) := by
  have h := reflection_log_2935_neg
  have he : Real.log (593996149133 / 500000000000) = -Real.log (500000000000 / 593996149133) := by
    rw [show ((593996149133 / 500000000000) : ℝ) = ((500000000000 / 593996149133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2936_neg : (10794503 / 62500000) ≤ -Real.log (2500000000 / 2971309547) ∧
    -Real.log (2500000000 / 2971309547) ≤ (172712049 / 1000000000) := by
  have h := checkLog_sound (w := (471309547 / 5471309547)) (n := 12)
    (lo := (10794503 / 62500000)) (hi := (172712049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2971309547 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2971309547 / 2500000000) = 1/(2500000000 / 2971309547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2936 : Bounds (10794503 / 62500000) (172712049 / 1000000000) (Real.log (2971309547 / 2500000000)) := by
  have h := reflection_log_2936_neg
  have he : Real.log (2971309547 / 2500000000) = -Real.log (2500000000 / 2971309547) := by
    rw [show ((2971309547 / 2500000000) : ℝ) = ((2500000000 / 2971309547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2937_neg : (86399809 / 250000000) ≤ -Real.log (31250000000 / 44151134033) ∧
    -Real.log (31250000000 / 44151134033) ≤ (345599237 / 1000000000) := by
  have h := checkLog_sound (w := (12901134033 / 75401134033)) (n := 12)
    (lo := (86399809 / 250000000)) (hi := (345599237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44151134033 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44151134033 / 31250000000) = 1/(31250000000 / 44151134033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2937 : Bounds (86399809 / 250000000) (345599237 / 1000000000) (Real.log (44151134033 / 31250000000)) := by
  have h := reflection_log_2937_neg
  have he : Real.log (44151134033 / 31250000000) = -Real.log (31250000000 / 44151134033) := by
    rw [show ((44151134033 / 31250000000) : ℝ) = ((31250000000 / 44151134033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2938_neg : (345805271 / 1000000000) ≤ -Real.log (125000000000 / 176640926641) ∧
    -Real.log (125000000000 / 176640926641) ≤ (43225659 / 125000000) := by
  have h := checkLog_sound (w := (51640926641 / 301640926641)) (n := 12)
    (lo := (345805271 / 1000000000)) (hi := (43225659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176640926641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176640926641 / 125000000000) = 1/(125000000000 / 176640926641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2938 : Bounds (345805271 / 1000000000) (43225659 / 125000000) (Real.log (176640926641 / 125000000000)) := by
  have h := reflection_log_2938_neg
  have he : Real.log (176640926641 / 125000000000) = -Real.log (125000000000 / 176640926641) := by
    rw [show ((176640926641 / 125000000000) : ℝ) = ((125000000000 / 176640926641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2939_neg : (158114243 / 1000000000) ≤ -Real.log (10000 / 11713) ∧
    -Real.log (10000 / 11713) ≤ (39528561 / 250000000) := by
  have h := checkLog_sound (w := (1713 / 21713)) (n := 12)
    (lo := (158114243 / 1000000000)) (hi := (39528561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11713 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11713 / 10000) = 1/(10000 / 11713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2939 : Bounds (158114243 / 1000000000) (39528561 / 250000000) (Real.log (11713 / 10000)) := by
  have h := reflection_log_2939_neg
  have he : Real.log (11713 / 10000) = -Real.log (10000 / 11713) := by
    rw [show ((11713 / 10000) : ℝ) = ((10000 / 11713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2940_neg : (187897071 / 1000000000) ≤ -Real.log (8287 / 10000) ∧
    -Real.log (8287 / 10000) ≤ (11743567 / 62500000) := by
  have h := checkLog_sound (w := (1713 / 18287)) (n := 12)
    (lo := (187897071 / 1000000000)) (hi := (11743567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8287) = 1/(8287 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2940 : Bounds (-11743567 / 62500000) (-187897071 / 1000000000) (Real.log (8287 / 10000)) := by
  have h := reflection_log_2940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2941_neg : (34257 / 200000000) ≤ -Real.log (10000000 / 10001713) ∧
    -Real.log (10000000 / 10001713) ≤ (85643 / 500000000) := by
  have h := checkLog_sound (w := (1713 / 20001713)) (n := 12)
    (lo := (34257 / 200000000)) (hi := (85643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001713 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001713 / 10000000) = 1/(10000000 / 10001713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2941 : Bounds (34257 / 200000000) (85643 / 500000000) (Real.log (10001713 / 10000000)) := by
  have h := reflection_log_2941_neg
  have he : Real.log (10001713 / 10000000) = -Real.log (10000000 / 10001713) := by
    rw [show ((10001713 / 10000000) : ℝ) = ((10000000 / 10001713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2942_neg : (85657 / 500000000) ≤ -Real.log (9998287 / 10000000) ∧
    -Real.log (9998287 / 10000000) ≤ (34263 / 200000000) := by
  have h := checkLog_sound (w := (1713 / 19998287)) (n := 12)
    (lo := (85657 / 500000000)) (hi := (34263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998287) = 1/(9998287 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2942 : Bounds (-34263 / 200000000) (-85657 / 500000000) (Real.log (9998287 / 10000000)) := by
  have h := reflection_log_2942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2943_neg : (82474517 / 1000000000) ≤ -Real.log (1000000 / 1085971) ∧
    -Real.log (1000000 / 1085971) ≤ (41237259 / 500000000) := by
  have h := checkLog_sound (w := (85971 / 2085971)) (n := 12)
    (lo := (82474517 / 1000000000)) (hi := (41237259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085971 / 1000000) = 1/(1000000 / 1085971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2943 : Bounds (82474517 / 1000000000) (41237259 / 500000000) (Real.log (1085971 / 1000000)) := by
  have h := reflection_log_2943_neg
  have he : Real.log (1085971 / 1000000) = -Real.log (1000000 / 1085971) := by
    rw [show ((1085971 / 1000000) : ℝ) = ((1000000 / 1085971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


