-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0169__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0169__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:32:10.289083+00:00
-- url     : https://prove2.me/theorems/5722bc53-fdf4-4969-ae3e-82317cecb2c1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0169 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0170, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0169 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0170, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0171)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0169 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0170, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0171)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0169 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0170, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0171) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0169 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0170, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0171).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0169 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10816_neg : (77881451 / 200000000) ≤ -Real.log (50000000000 / 73805279057) ∧
    -Real.log (50000000000 / 73805279057) ≤ (48675907 / 125000000) := by
  have h := checkLog_sound (w := (23805279057 / 123805279057)) (n := 12)
    (lo := (77881451 / 200000000)) (hi := (48675907 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73805279057 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73805279057 / 50000000000) = 1/(50000000000 / 73805279057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10816 : Bounds (77881451 / 200000000) (48675907 / 125000000) (Real.log (73805279057 / 50000000000)) := by
  have h := reflection_log_10816_neg
  have he : Real.log (73805279057 / 50000000000) = -Real.log (50000000000 / 73805279057) := by
    rw [show ((73805279057 / 50000000000) : ℝ) = ((50000000000 / 73805279057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10817_neg : (195645619 / 500000000) ≤ -Real.log (100000000000 / 147888916019) ∧
    -Real.log (100000000000 / 147888916019) ≤ (391291239 / 1000000000) := by
  have h := checkLog_sound (w := (47888916019 / 247888916019)) (n := 12)
    (lo := (195645619 / 500000000)) (hi := (391291239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147888916019 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147888916019 / 100000000000) = 1/(100000000000 / 147888916019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10817 : Bounds (195645619 / 500000000) (391291239 / 1000000000) (Real.log (147888916019 / 100000000000)) := by
  have h := reflection_log_10817_neg
  have he : Real.log (147888916019 / 100000000000) = -Real.log (100000000000 / 147888916019) := by
    rw [show ((147888916019 / 100000000000) : ℝ) = ((100000000000 / 147888916019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10818_neg : (790785649 / 1000000000) ≤ -Real.log (100000000000 / 220512820513) ∧
    -Real.log (100000000000 / 220512820513) ≤ (790785651 / 1000000000) := by
  have h := checkLog_sound (w := (20512820513 / 420512820513)) (n := 12)
    (lo := (97638469 / 1000000000)) (hi := (9763847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220512820513 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(220512820513 / 200000000000) = 1/(100000000000 / 220512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10818 : Bounds (790785649 / 1000000000) (790785651 / 1000000000) (Real.log (220512820513 / 100000000000)) := by
  have h := reflection_log_10818_neg
  have he : Real.log (220512820513 / 100000000000) = -Real.log (100000000000 / 220512820513) := by
    rw [show ((220512820513 / 100000000000) : ℝ) = ((100000000000 / 220512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10819_neg : (319907219 / 1000000000) ≤ -Real.log (1000 / 1377) ∧
    -Real.log (1000 / 1377) ≤ (15995361 / 50000000) := by
  have h := checkLog_sound (w := (377 / 2377)) (n := 12)
    (lo := (319907219 / 1000000000)) (hi := (15995361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377 / 1000) = 1/(1000 / 1377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10819 : Bounds (319907219 / 1000000000) (15995361 / 50000000) (Real.log (1377 / 1000)) := by
  have h := reflection_log_10819_neg
  have he : Real.log (1377 / 1000) = -Real.log (1000 / 1377) := by
    rw [show ((1377 / 1000) : ℝ) = ((1000 / 1377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10820_neg : (11830219 / 25000000) ≤ -Real.log (623 / 1000) ∧
    -Real.log (623 / 1000) ≤ (473208761 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 1623)) (n := 12)
    (lo := (11830219 / 25000000)) (hi := (473208761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 623) = 1/(623 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10820 : Bounds (-473208761 / 1000000000) (-11830219 / 25000000) (Real.log (623 / 1000)) := by
  have h := reflection_log_10820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10821_neg : (11779 / 31250000) ≤ -Real.log (1000000 / 1000377) ∧
    -Real.log (1000000 / 1000377) ≤ (376929 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2000377)) (n := 12)
    (lo := (11779 / 31250000)) (hi := (376929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000377 / 1000000) = 1/(1000000 / 1000377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10821 : Bounds (11779 / 31250000) (376929 / 1000000000) (Real.log (1000377 / 1000000)) := by
  have h := reflection_log_10821_neg
  have he : Real.log (1000377 / 1000000) = -Real.log (1000000 / 1000377) := by
    rw [show ((1000377 / 1000000) : ℝ) = ((1000000 / 1000377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10822_neg : (377071 / 1000000000) ≤ -Real.log (999623 / 1000000) ∧
    -Real.log (999623 / 1000000) ≤ (23567 / 62500000) := by
  have h := checkLog_sound (w := (377 / 1999623)) (n := 12)
    (lo := (377071 / 1000000000)) (hi := (23567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999623) = 1/(999623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10822 : Bounds (-23567 / 62500000) (-377071 / 1000000000) (Real.log (999623 / 1000000)) := by
  have h := reflection_log_10822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10823_neg : (176321089 / 1000000000) ≤ -Real.log (1000000 / 1192821) ∧
    -Real.log (1000000 / 1192821) ≤ (17632109 / 100000000) := by
  have h := checkLog_sound (w := (192821 / 2192821)) (n := 12)
    (lo := (176321089 / 1000000000)) (hi := (17632109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192821 / 1000000) = 1/(1000000 / 1192821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10823 : Bounds (176321089 / 1000000000) (17632109 / 100000000) (Real.log (1192821 / 1000000)) := by
  have h := reflection_log_10823_neg
  have he : Real.log (1192821 / 1000000) = -Real.log (1000000 / 1192821) := by
    rw [show ((1192821 / 1000000) : ℝ) = ((1000000 / 1192821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10824_neg : (107104913 / 500000000) ≤ -Real.log (807179 / 1000000) ∧
    -Real.log (807179 / 1000000) ≤ (214209827 / 1000000000) := by
  have h := checkLog_sound (w := (192821 / 1807179)) (n := 12)
    (lo := (107104913 / 500000000)) (hi := (214209827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807179) = 1/(807179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10824 : Bounds (-214209827 / 1000000000) (-107104913 / 500000000) (Real.log (807179 / 1000000)) := by
  have h := reflection_log_10824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10825_neg : (177082021 / 1000000000) ≤ -Real.log (1000000 / 1193729) ∧
    -Real.log (1000000 / 1193729) ≤ (88541011 / 500000000) := by
  have h := checkLog_sound (w := (193729 / 2193729)) (n := 12)
    (lo := (177082021 / 1000000000)) (hi := (88541011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193729 / 1000000) = 1/(1000000 / 1193729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10825 : Bounds (177082021 / 1000000000) (88541011 / 500000000) (Real.log (1193729 / 1000000)) := by
  have h := reflection_log_10825_neg
  have he : Real.log (1193729 / 1000000) = -Real.log (1000000 / 1193729) := by
    rw [show ((1193729 / 1000000) : ℝ) = ((1000000 / 1193729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10826_neg : (53833841 / 250000000) ≤ -Real.log (806271 / 1000000) ∧
    -Real.log (806271 / 1000000) ≤ (43067073 / 200000000) := by
  have h := checkLog_sound (w := (193729 / 1806271)) (n := 12)
    (lo := (53833841 / 250000000)) (hi := (43067073 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806271) = 1/(806271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10826 : Bounds (-43067073 / 200000000) (-53833841 / 250000000) (Real.log (806271 / 1000000)) := by
  have h := reflection_log_10826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10827_neg : (38253343 / 1000000000) ≤ -Real.log (962469074559 / 1000000000000) ∧
    -Real.log (962469074559 / 1000000000000) ≤ (1195417 / 31250000) := by
  have h := checkLog_sound (w := (37530925441 / 1962469074559)) (n := 12)
    (lo := (38253343 / 1000000000)) (hi := (1195417 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962469074559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962469074559) = 1/(962469074559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10827 : Bounds (-1195417 / 31250000) (-38253343 / 1000000000) (Real.log (962469074559 / 1000000000000)) := by
  have h := reflection_log_10827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10828_neg : (1184023 / 31250000) ≤ -Real.log (962820061959 / 1000000000000) ∧
    -Real.log (962820061959 / 1000000000000) ≤ (37888737 / 1000000000) := by
  have h := checkLog_sound (w := (37179938041 / 1962820061959)) (n := 12)
    (lo := (1184023 / 31250000)) (hi := (37888737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962820061959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962820061959) = 1/(962820061959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10828 : Bounds (-37888737 / 1000000000) (-1184023 / 31250000) (Real.log (962820061959 / 1000000000000)) := by
  have h := reflection_log_10828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10829_neg : (97632729 / 250000000) ≤ -Real.log (50000000000 / 73888257747) ∧
    -Real.log (50000000000 / 73888257747) ≤ (390530917 / 1000000000) := by
  have h := checkLog_sound (w := (23888257747 / 123888257747)) (n := 12)
    (lo := (97632729 / 250000000)) (hi := (390530917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73888257747 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73888257747 / 50000000000) = 1/(50000000000 / 73888257747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10829 : Bounds (97632729 / 250000000) (390530917 / 1000000000) (Real.log (73888257747 / 50000000000)) := by
  have h := reflection_log_10829_neg
  have he : Real.log (73888257747 / 50000000000) = -Real.log (50000000000 / 73888257747) := by
    rw [show ((73888257747 / 50000000000) : ℝ) = ((50000000000 / 73888257747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10830_neg : (78483477 / 200000000) ≤ -Real.log (50000000000 / 74027777261) ∧
    -Real.log (50000000000 / 74027777261) ≤ (196208693 / 500000000) := by
  have h := checkLog_sound (w := (24027777261 / 124027777261)) (n := 12)
    (lo := (78483477 / 200000000)) (hi := (196208693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74027777261 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74027777261 / 50000000000) = 1/(50000000000 / 74027777261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10830 : Bounds (78483477 / 200000000) (196208693 / 500000000) (Real.log (74027777261 / 50000000000)) := by
  have h := reflection_log_10830_neg
  have he : Real.log (74027777261 / 50000000000) = -Real.log (50000000000 / 74027777261) := by
    rw [show ((74027777261 / 50000000000) : ℝ) = ((50000000000 / 74027777261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10831_neg : (790785649 / 1000000000) ≤ -Real.log (125000000000 / 275641025641) ∧
    -Real.log (125000000000 / 275641025641) ≤ (790785651 / 1000000000) := by
  have h := checkLog_sound (w := (25641025641 / 525641025641)) (n := 12)
    (lo := (97638469 / 1000000000)) (hi := (9763847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275641025641 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275641025641 / 250000000000) = 1/(125000000000 / 275641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10831 : Bounds (790785649 / 1000000000) (790785651 / 1000000000) (Real.log (275641025641 / 125000000000)) := by
  have h := reflection_log_10831_neg
  have he : Real.log (275641025641 / 125000000000) = -Real.log (125000000000 / 275641025641) := by
    rw [show ((275641025641 / 125000000000) : ℝ) = ((125000000000 / 275641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10832_neg : (793115979 / 1000000000) ≤ -Real.log (250000000000 / 552568218299) ∧
    -Real.log (250000000000 / 552568218299) ≤ (793115981 / 1000000000) := by
  have h := checkLog_sound (w := (52568218299 / 1052568218299)) (n := 12)
    (lo := (99968799 / 1000000000)) (hi := (124961 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552568218299 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(552568218299 / 500000000000) = 1/(250000000000 / 552568218299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10832 : Bounds (793115979 / 1000000000) (793115981 / 1000000000) (Real.log (552568218299 / 250000000000)) := by
  have h := reflection_log_10832_neg
  have he : Real.log (552568218299 / 250000000000) = -Real.log (250000000000 / 552568218299) := by
    rw [show ((552568218299 / 250000000000) : ℝ) = ((250000000000 / 552568218299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10833_neg : (80158293 / 250000000) ≤ -Real.log (500 / 689) ∧
    -Real.log (500 / 689) ≤ (320633173 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 1189)) (n := 12)
    (lo := (80158293 / 250000000)) (hi := (320633173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 500) = 1/(500 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10833 : Bounds (80158293 / 250000000) (320633173 / 1000000000) (Real.log (689 / 500)) := by
  have h := reflection_log_10833_neg
  have he : Real.log (689 / 500) = -Real.log (500 / 689) := by
    rw [show ((689 / 500) : ℝ) = ((500 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10834_neg : (237407593 / 500000000) ≤ -Real.log (311 / 500) ∧
    -Real.log (311 / 500) ≤ (474815187 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 811)) (n := 12)
    (lo := (237407593 / 500000000)) (hi := (474815187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 311) = 1/(311 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10834 : Bounds (-474815187 / 1000000000) (-237407593 / 500000000) (Real.log (311 / 500)) := by
  have h := reflection_log_10834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10835_neg : (47241 / 125000000) ≤ -Real.log (500000 / 500189) ∧
    -Real.log (500000 / 500189) ≤ (377929 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 1000189)) (n := 12)
    (lo := (47241 / 125000000)) (hi := (377929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500189 / 500000) = 1/(500000 / 500189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10835 : Bounds (47241 / 125000000) (377929 / 1000000000) (Real.log (500189 / 500000)) := by
  have h := reflection_log_10835_neg
  have he : Real.log (500189 / 500000) = -Real.log (500000 / 500189) := by
    rw [show ((500189 / 500000) : ℝ) = ((500000 / 500189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10836_neg : (378071 / 1000000000) ≤ -Real.log (499811 / 500000) ∧
    -Real.log (499811 / 500000) ≤ (47259 / 125000000) := by
  have h := checkLog_sound (w := (189 / 999811)) (n := 12)
    (lo := (378071 / 1000000000)) (hi := (47259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499811) = 1/(499811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10836 : Bounds (-47259 / 125000000) (-378071 / 1000000000) (Real.log (499811 / 500000)) := by
  have h := reflection_log_10836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10837_neg : (35354739 / 200000000) ≤ -Real.log (1000000 / 1193361) ∧
    -Real.log (1000000 / 1193361) ≤ (2762089 / 15625000) := by
  have h := checkLog_sound (w := (193361 / 2193361)) (n := 12)
    (lo := (35354739 / 200000000)) (hi := (2762089 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193361 / 1000000) = 1/(1000000 / 1193361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10837 : Bounds (35354739 / 200000000) (2762089 / 15625000) (Real.log (1193361 / 1000000)) := by
  have h := reflection_log_10837_neg
  have he : Real.log (1193361 / 1000000) = -Real.log (1000000 / 1193361) := by
    rw [show ((1193361 / 1000000) : ℝ) = ((1000000 / 1193361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10838_neg : (107439523 / 500000000) ≤ -Real.log (806639 / 1000000) ∧
    -Real.log (806639 / 1000000) ≤ (214879047 / 1000000000) := by
  have h := checkLog_sound (w := (193361 / 1806639)) (n := 12)
    (lo := (107439523 / 500000000)) (hi := (214879047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806639) = 1/(806639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10838 : Bounds (-214879047 / 1000000000) (-107439523 / 500000000) (Real.log (806639 / 1000000)) := by
  have h := reflection_log_10838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10839_neg : (177535957 / 1000000000) ≤ -Real.log (1000000 / 1194271) ∧
    -Real.log (1000000 / 1194271) ≤ (88767979 / 500000000) := by
  have h := checkLog_sound (w := (194271 / 2194271)) (n := 12)
    (lo := (177535957 / 1000000000)) (hi := (88767979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194271 / 1000000) = 1/(1000000 / 1194271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10839 : Bounds (177535957 / 1000000000) (88767979 / 500000000) (Real.log (1194271 / 1000000)) := by
  have h := reflection_log_10839_neg
  have he : Real.log (1194271 / 1000000) = -Real.log (1000000 / 1194271) := by
    rw [show ((1194271 / 1000000) : ℝ) = ((1000000 / 1194271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10840_neg : (216007821 / 1000000000) ≤ -Real.log (805729 / 1000000) ∧
    -Real.log (805729 / 1000000) ≤ (108003911 / 500000000) := by
  have h := checkLog_sound (w := (194271 / 1805729)) (n := 12)
    (lo := (216007821 / 1000000000)) (hi := (108003911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805729) = 1/(805729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10840 : Bounds (-108003911 / 500000000) (-216007821 / 1000000000) (Real.log (805729 / 1000000)) := by
  have h := reflection_log_10840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10841_neg : (38471863 / 1000000000) ≤ -Real.log (962258778559 / 1000000000000) ∧
    -Real.log (962258778559 / 1000000000000) ≤ (4808983 / 125000000) := by
  have h := checkLog_sound (w := (37741221441 / 1962258778559)) (n := 12)
    (lo := (38471863 / 1000000000)) (hi := (4808983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962258778559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962258778559) = 1/(962258778559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10841 : Bounds (-4808983 / 125000000) (-38471863 / 1000000000) (Real.log (962258778559 / 1000000000000)) := by
  have h := reflection_log_10841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10842_neg : (762107 / 20000000) ≤ -Real.log (962611523679 / 1000000000000) ∧
    -Real.log (962611523679 / 1000000000000) ≤ (38105351 / 1000000000) := by
  have h := checkLog_sound (w := (37388476321 / 1962611523679)) (n := 12)
    (lo := (762107 / 20000000)) (hi := (38105351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962611523679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962611523679) = 1/(962611523679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10842 : Bounds (-38105351 / 1000000000) (-762107 / 20000000) (Real.log (962611523679 / 1000000000000)) := by
  have h := reflection_log_10842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10843_neg : (195826371 / 500000000) ≤ -Real.log (500000000000 / 739711940533) ∧
    -Real.log (500000000000 / 739711940533) ≤ (391652743 / 1000000000) := by
  have h := checkLog_sound (w := (239711940533 / 1239711940533)) (n := 12)
    (lo := (195826371 / 500000000)) (hi := (391652743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739711940533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739711940533 / 500000000000) = 1/(500000000000 / 739711940533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10843 : Bounds (195826371 / 500000000) (391652743 / 1000000000) (Real.log (739711940533 / 500000000000)) := by
  have h := reflection_log_10843_neg
  have he : Real.log (739711940533 / 500000000000) = -Real.log (500000000000 / 739711940533) := by
    rw [show ((739711940533 / 500000000000) : ℝ) = ((500000000000 / 739711940533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10844_neg : (196771889 / 500000000) ≤ -Real.log (250000000000 / 370556043037) ∧
    -Real.log (250000000000 / 370556043037) ≤ (393543779 / 1000000000) := by
  have h := checkLog_sound (w := (120556043037 / 620556043037)) (n := 12)
    (lo := (196771889 / 500000000)) (hi := (393543779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370556043037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370556043037 / 250000000000) = 1/(250000000000 / 370556043037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10844 : Bounds (196771889 / 500000000) (393543779 / 1000000000) (Real.log (370556043037 / 250000000000)) := by
  have h := reflection_log_10844_neg
  have he : Real.log (370556043037 / 250000000000) = -Real.log (250000000000 / 370556043037) := by
    rw [show ((370556043037 / 250000000000) : ℝ) = ((250000000000 / 370556043037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10845_neg : (793115979 / 1000000000) ≤ -Real.log (500000000000 / 1105136436597) ∧
    -Real.log (500000000000 / 1105136436597) ≤ (793115981 / 1000000000) := by
  have h := checkLog_sound (w := (105136436597 / 2105136436597)) (n := 12)
    (lo := (99968799 / 1000000000)) (hi := (124961 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105136436597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1105136436597 / 1000000000000) = 1/(500000000000 / 1105136436597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10845 : Bounds (793115979 / 1000000000) (793115981 / 1000000000) (Real.log (1105136436597 / 500000000000)) := by
  have h := reflection_log_10845_neg
  have he : Real.log (1105136436597 / 500000000000) = -Real.log (500000000000 / 1105136436597) := by
    rw [show ((1105136436597 / 500000000000) : ℝ) = ((500000000000 / 1105136436597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10846_neg : (397724179 / 500000000) ≤ -Real.log (500000000000 / 1107717041801) ∧
    -Real.log (500000000000 / 1107717041801) ≤ (19886209 / 25000000) := by
  have h := checkLog_sound (w := (107717041801 / 2107717041801)) (n := 12)
    (lo := (51150589 / 500000000)) (hi := (102301179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107717041801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1107717041801 / 1000000000000) = 1/(500000000000 / 1107717041801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10846 : Bounds (397724179 / 500000000) (19886209 / 25000000) (Real.log (1107717041801 / 500000000000)) := by
  have h := reflection_log_10846_neg
  have he : Real.log (1107717041801 / 500000000000) = -Real.log (500000000000 / 1107717041801) := by
    rw [show ((1107717041801 / 500000000000) : ℝ) = ((500000000000 / 1107717041801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10847_neg : (160679299 / 500000000) ≤ -Real.log (1000 / 1379) ∧
    -Real.log (1000 / 1379) ≤ (321358599 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 2379)) (n := 12)
    (lo := (160679299 / 500000000)) (hi := (321358599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1000) = 1/(1000 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10847 : Bounds (160679299 / 500000000) (321358599 / 1000000000) (Real.log (1379 / 1000)) := by
  have h := reflection_log_10847_neg
  have he : Real.log (1379 / 1000) = -Real.log (1000 / 1379) := by
    rw [show ((1379 / 1000) : ℝ) = ((1000 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10848_neg : (476424197 / 1000000000) ≤ -Real.log (621 / 1000) ∧
    -Real.log (621 / 1000) ≤ (238212099 / 500000000) := by
  have h := checkLog_sound (w := (379 / 1621)) (n := 12)
    (lo := (476424197 / 1000000000)) (hi := (238212099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 621) = 1/(621 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10848 : Bounds (-238212099 / 500000000) (-476424197 / 1000000000) (Real.log (621 / 1000)) := by
  have h := reflection_log_10848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10849_neg : (23683 / 62500000) ≤ -Real.log (1000000 / 1000379) ∧
    -Real.log (1000000 / 1000379) ≤ (378929 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 2000379)) (n := 12)
    (lo := (23683 / 62500000)) (hi := (378929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000379 / 1000000) = 1/(1000000 / 1000379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10849 : Bounds (23683 / 62500000) (378929 / 1000000000) (Real.log (1000379 / 1000000)) := by
  have h := reflection_log_10849_neg
  have he : Real.log (1000379 / 1000000) = -Real.log (1000000 / 1000379) := by
    rw [show ((1000379 / 1000000) : ℝ) = ((1000000 / 1000379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10850_neg : (379071 / 1000000000) ≤ -Real.log (999621 / 1000000) ∧
    -Real.log (999621 / 1000000) ≤ (5923 / 15625000) := by
  have h := checkLog_sound (w := (379 / 1999621)) (n := 12)
    (lo := (379071 / 1000000000)) (hi := (5923 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999621) = 1/(999621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10850 : Bounds (-5923 / 15625000) (-379071 / 1000000000) (Real.log (999621 / 1000000)) := by
  have h := reflection_log_10850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10851_neg : (88613467 / 500000000) ≤ -Real.log (500000 / 596951) ∧
    -Real.log (500000 / 596951) ≤ (35445387 / 200000000) := by
  have h := checkLog_sound (w := (96951 / 1096951)) (n := 12)
    (lo := (88613467 / 500000000)) (hi := (35445387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596951 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596951 / 500000) = 1/(500000 / 596951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10851 : Bounds (88613467 / 500000000) (35445387 / 200000000) (Real.log (596951 / 500000)) := by
  have h := reflection_log_10851_neg
  have he : Real.log (596951 / 500000) = -Real.log (500000 / 596951) := by
    rw [show ((596951 / 500000) : ℝ) = ((500000 / 596951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10852_neg : (43109991 / 200000000) ≤ -Real.log (403049 / 500000) ∧
    -Real.log (403049 / 500000) ≤ (53887489 / 250000000) := by
  have h := checkLog_sound (w := (96951 / 903049)) (n := 12)
    (lo := (43109991 / 200000000)) (hi := (53887489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403049) = 1/(403049 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10852 : Bounds (-53887489 / 250000000) (-43109991 / 200000000) (Real.log (403049 / 500000)) := by
  have h := reflection_log_10852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10853_neg : (177989687 / 1000000000) ≤ -Real.log (1000000 / 1194813) ∧
    -Real.log (1000000 / 1194813) ≤ (22248711 / 125000000) := by
  have h := checkLog_sound (w := (194813 / 2194813)) (n := 12)
    (lo := (177989687 / 1000000000)) (hi := (22248711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194813 / 1000000) = 1/(1000000 / 1194813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10853 : Bounds (177989687 / 1000000000) (22248711 / 125000000) (Real.log (1194813 / 1000000)) := by
  have h := reflection_log_10853_neg
  have he : Real.log (1194813 / 1000000) = -Real.log (1000000 / 1194813) := by
    rw [show ((1194813 / 1000000) : ℝ) = ((1000000 / 1194813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10854_neg : (21668073 / 100000000) ≤ -Real.log (805187 / 1000000) ∧
    -Real.log (805187 / 1000000) ≤ (216680731 / 1000000000) := by
  have h := checkLog_sound (w := (194813 / 1805187)) (n := 12)
    (lo := (21668073 / 100000000)) (hi := (216680731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805187) = 1/(805187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10854 : Bounds (-216680731 / 1000000000) (-21668073 / 100000000) (Real.log (805187 / 1000000)) := by
  have h := reflection_log_10854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10855_neg : (19345521 / 500000000) ≤ -Real.log (962047895031 / 1000000000000) ∧
    -Real.log (962047895031 / 1000000000000) ≤ (38691043 / 1000000000) := by
  have h := checkLog_sound (w := (37952104969 / 1962047895031)) (n := 12)
    (lo := (19345521 / 500000000)) (hi := (38691043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962047895031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962047895031) = 1/(962047895031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10855 : Bounds (-38691043 / 1000000000) (-19345521 / 500000000) (Real.log (962047895031 / 1000000000000)) := by
  have h := reflection_log_10855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10856_neg : (38323021 / 1000000000) ≤ -Real.log (240600503599 / 250000000000) ∧
    -Real.log (240600503599 / 250000000000) ≤ (19161511 / 500000000) := by
  have h := checkLog_sound (w := (9399496401 / 490600503599)) (n := 12)
    (lo := (38323021 / 1000000000)) (hi := (19161511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240600503599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240600503599) = 1/(240600503599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10856 : Bounds (-19161511 / 500000000) (-38323021 / 1000000000) (Real.log (240600503599 / 250000000000)) := by
  have h := reflection_log_10856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10857_neg : (39277689 / 100000000) ≤ -Real.log (31250000000 / 46283997107) ∧
    -Real.log (31250000000 / 46283997107) ≤ (392776891 / 1000000000) := by
  have h := checkLog_sound (w := (15033997107 / 77533997107)) (n := 12)
    (lo := (39277689 / 100000000)) (hi := (392776891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46283997107 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46283997107 / 31250000000) = 1/(31250000000 / 46283997107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10857 : Bounds (39277689 / 100000000) (392776891 / 1000000000) (Real.log (46283997107 / 31250000000)) := by
  have h := reflection_log_10857_neg
  have he : Real.log (46283997107 / 31250000000) = -Real.log (31250000000 / 46283997107) := by
    rw [show ((46283997107 / 31250000000) : ℝ) = ((31250000000 / 46283997107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10858_neg : (197335209 / 500000000) ≤ -Real.log (2000000000 / 2967790091) ∧
    -Real.log (2000000000 / 2967790091) ≤ (394670419 / 1000000000) := by
  have h := checkLog_sound (w := (967790091 / 4967790091)) (n := 12)
    (lo := (197335209 / 500000000)) (hi := (394670419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2967790091 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2967790091 / 2000000000) = 1/(2000000000 / 2967790091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10858 : Bounds (197335209 / 500000000) (394670419 / 1000000000) (Real.log (2967790091 / 2000000000)) := by
  have h := reflection_log_10858_neg
  have he : Real.log (2967790091 / 2000000000) = -Real.log (2000000000 / 2967790091) := by
    rw [show ((2967790091 / 2000000000) : ℝ) = ((2000000000 / 2967790091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10859_neg : (397724179 / 500000000) ≤ -Real.log (2500000000 / 5538585209) ∧
    -Real.log (2500000000 / 5538585209) ≤ (19886209 / 25000000) := by
  have h := checkLog_sound (w := (538585209 / 10538585209)) (n := 12)
    (lo := (51150589 / 500000000)) (hi := (102301179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5538585209 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5538585209 / 5000000000) = 1/(2500000000 / 5538585209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10859 : Bounds (397724179 / 500000000) (19886209 / 25000000) (Real.log (5538585209 / 2500000000)) := by
  have h := reflection_log_10859_neg
  have he : Real.log (5538585209 / 2500000000) = -Real.log (2500000000 / 5538585209) := by
    rw [show ((5538585209 / 2500000000) : ℝ) = ((2500000000 / 5538585209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10860_neg : (159556559 / 200000000) ≤ -Real.log (500000000000 / 1110305958133) ∧
    -Real.log (500000000000 / 1110305958133) ≤ (797782797 / 1000000000) := by
  have h := checkLog_sound (w := (110305958133 / 2110305958133)) (n := 12)
    (lo := (20927123 / 200000000)) (hi := (3269863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110305958133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110305958133 / 1000000000000) = 1/(500000000000 / 1110305958133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10860 : Bounds (159556559 / 200000000) (797782797 / 1000000000) (Real.log (1110305958133 / 500000000000)) := by
  have h := reflection_log_10860_neg
  have he : Real.log (1110305958133 / 500000000000) = -Real.log (500000000000 / 1110305958133) := by
    rw [show ((1110305958133 / 500000000000) : ℝ) = ((500000000000 / 1110305958133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10861_neg : (322083499 / 1000000000) ≤ -Real.log (50 / 69) ∧
    -Real.log (50 / 69) ≤ (644167 / 2000000) := by
  have h := checkLog_sound (w := (19 / 119)) (n := 12)
    (lo := (322083499 / 1000000000)) (hi := (644167 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69 / 50) = 1/(50 / 69) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10861 : Bounds (322083499 / 1000000000) (644167 / 2000000) (Real.log (69 / 50)) := by
  have h := reflection_log_10861_neg
  have he : Real.log (69 / 50) = -Real.log (50 / 69) := by
    rw [show ((69 / 50) : ℝ) = ((50 / 69) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10862_neg : (2390179 / 5000000) ≤ -Real.log (31 / 50) ∧
    -Real.log (31 / 50) ≤ (478035801 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 81)) (n := 12)
    (lo := (2390179 / 5000000)) (hi := (478035801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 31) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 31) = 1/(31 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10862 : Bounds (-478035801 / 1000000000) (-2390179 / 5000000) (Real.log (31 / 50)) := by
  have h := reflection_log_10862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10863_neg : (379927 / 1000000000) ≤ -Real.log (50000 / 50019) ∧
    -Real.log (50000 / 50019) ≤ (47491 / 125000000) := by
  have h := checkLog_sound (w := (19 / 100019)) (n := 12)
    (lo := (379927 / 1000000000)) (hi := (47491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50019 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50019 / 50000) = 1/(50000 / 50019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10863 : Bounds (379927 / 1000000000) (47491 / 125000000) (Real.log (50019 / 50000)) := by
  have h := reflection_log_10863_neg
  have he : Real.log (50019 / 50000) = -Real.log (50000 / 50019) := by
    rw [show ((50019 / 50000) : ℝ) = ((50000 / 50019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10864_neg : (47509 / 125000000) ≤ -Real.log (49981 / 50000) ∧
    -Real.log (49981 / 50000) ≤ (380073 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 99981)) (n := 12)
    (lo := (47509 / 125000000)) (hi := (380073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49981) = 1/(49981 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10864 : Bounds (-380073 / 1000000000) (-47509 / 125000000) (Real.log (49981 / 50000)) := by
  have h := reflection_log_10864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10865_neg : (35536161 / 200000000) ≤ -Real.log (250000 / 298611) ∧
    -Real.log (250000 / 298611) ≤ (88840403 / 500000000) := by
  have h := checkLog_sound (w := (48611 / 548611)) (n := 12)
    (lo := (35536161 / 200000000)) (hi := (88840403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298611 / 250000) = 1/(250000 / 298611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10865 : Bounds (35536161 / 200000000) (88840403 / 500000000) (Real.log (298611 / 250000)) := by
  have h := reflection_log_10865_neg
  have he : Real.log (298611 / 250000) = -Real.log (250000 / 298611) := by
    rw [show ((298611 / 250000) : ℝ) = ((250000 / 298611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10866_neg : (54055639 / 250000000) ≤ -Real.log (201389 / 250000) ∧
    -Real.log (201389 / 250000) ≤ (216222557 / 1000000000) := by
  have h := checkLog_sound (w := (48611 / 451389)) (n := 12)
    (lo := (54055639 / 250000000)) (hi := (216222557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201389) = 1/(201389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10866 : Bounds (-216222557 / 1000000000) (-54055639 / 250000000) (Real.log (201389 / 250000)) := by
  have h := reflection_log_10866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10867_neg : (44610803 / 250000000) ≤ -Real.log (200000 / 239071) ∧
    -Real.log (200000 / 239071) ≤ (178443213 / 1000000000) := by
  have h := checkLog_sound (w := (39071 / 439071)) (n := 12)
    (lo := (44610803 / 250000000)) (hi := (178443213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239071 / 200000) = 1/(200000 / 239071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10867 : Bounds (44610803 / 250000000) (178443213 / 1000000000) (Real.log (239071 / 200000)) := by
  have h := reflection_log_10867_neg
  have he : Real.log (239071 / 200000) = -Real.log (200000 / 239071) := by
    rw [show ((239071 / 200000) : ℝ) = ((200000 / 239071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10868_neg : (54338523 / 250000000) ≤ -Real.log (160929 / 200000) ∧
    -Real.log (160929 / 200000) ≤ (217354093 / 1000000000) := by
  have h := checkLog_sound (w := (39071 / 360929)) (n := 12)
    (lo := (54338523 / 250000000)) (hi := (217354093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160929) = 1/(160929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10868 : Bounds (-217354093 / 1000000000) (-54338523 / 250000000) (Real.log (160929 / 200000)) := by
  have h := reflection_log_10868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10869_neg : (243193 / 6250000) ≤ -Real.log (38473456959 / 40000000000) ∧
    -Real.log (38473456959 / 40000000000) ≤ (38910881 / 1000000000) := by
  have h := checkLog_sound (w := (1526543041 / 78473456959)) (n := 12)
    (lo := (243193 / 6250000)) (hi := (38910881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38473456959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38473456959) = 1/(38473456959 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10869 : Bounds (-38910881 / 1000000000) (-243193 / 6250000) (Real.log (38473456959 / 40000000000)) := by
  have h := reflection_log_10869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10870_neg : (38541751 / 1000000000) ≤ -Real.log (60136970679 / 62500000000) ∧
    -Real.log (60136970679 / 62500000000) ≤ (4817719 / 125000000) := by
  have h := checkLog_sound (w := (2363029321 / 122636970679)) (n := 12)
    (lo := (38541751 / 1000000000)) (hi := (4817719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60136970679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60136970679) = 1/(60136970679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10870 : Bounds (-4817719 / 125000000) (-38541751 / 1000000000) (Real.log (60136970679 / 62500000000)) := by
  have h := reflection_log_10870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10871_neg : (393903361 / 1000000000) ≤ -Real.log (250000000000 / 370689312723) ∧
    -Real.log (250000000000 / 370689312723) ≤ (196951681 / 500000000) := by
  have h := checkLog_sound (w := (120689312723 / 620689312723)) (n := 12)
    (lo := (393903361 / 1000000000)) (hi := (196951681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370689312723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370689312723 / 250000000000) = 1/(250000000000 / 370689312723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10871 : Bounds (393903361 / 1000000000) (196951681 / 500000000) (Real.log (370689312723 / 250000000000)) := by
  have h := reflection_log_10871_neg
  have he : Real.log (370689312723 / 250000000000) = -Real.log (250000000000 / 370689312723) := by
    rw [show ((370689312723 / 250000000000) : ℝ) = ((250000000000 / 370689312723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10872_neg : (79159461 / 200000000) ≤ -Real.log (125000000000 / 185696021227) ∧
    -Real.log (125000000000 / 185696021227) ≤ (197898653 / 500000000) := by
  have h := checkLog_sound (w := (60696021227 / 310696021227)) (n := 12)
    (lo := (79159461 / 200000000)) (hi := (197898653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185696021227 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185696021227 / 125000000000) = 1/(125000000000 / 185696021227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10872 : Bounds (79159461 / 200000000) (197898653 / 500000000) (Real.log (185696021227 / 125000000000)) := by
  have h := reflection_log_10872_neg
  have he : Real.log (185696021227 / 125000000000) = -Real.log (125000000000 / 185696021227) := by
    rw [show ((185696021227 / 125000000000) : ℝ) = ((125000000000 / 185696021227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10873_neg : (159556559 / 200000000) ≤ -Real.log (125000000000 / 277576489533) ∧
    -Real.log (125000000000 / 277576489533) ≤ (797782797 / 1000000000) := by
  have h := checkLog_sound (w := (27576489533 / 527576489533)) (n := 12)
    (lo := (20927123 / 200000000)) (hi := (3269863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277576489533 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(277576489533 / 250000000000) = 1/(125000000000 / 277576489533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10873 : Bounds (159556559 / 200000000) (797782797 / 1000000000) (Real.log (277576489533 / 125000000000)) := by
  have h := reflection_log_10873_neg
  have he : Real.log (277576489533 / 125000000000) = -Real.log (125000000000 / 277576489533) := by
    rw [show ((277576489533 / 125000000000) : ℝ) = ((125000000000 / 277576489533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10874_neg : (800119299 / 1000000000) ≤ -Real.log (500000000000 / 1112903225807) ∧
    -Real.log (500000000000 / 1112903225807) ≤ (800119301 / 1000000000) := by
  have h := checkLog_sound (w := (112903225807 / 2112903225807)) (n := 12)
    (lo := (106972119 / 1000000000)) (hi := (2674303 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112903225807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112903225807 / 1000000000000) = 1/(500000000000 / 1112903225807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10874 : Bounds (800119299 / 1000000000) (800119301 / 1000000000) (Real.log (1112903225807 / 500000000000)) := by
  have h := reflection_log_10874_neg
  have he : Real.log (1112903225807 / 500000000000) = -Real.log (500000000000 / 1112903225807) := by
    rw [show ((1112903225807 / 500000000000) : ℝ) = ((500000000000 / 1112903225807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10875_neg : (161403937 / 500000000) ≤ -Real.log (1000 / 1381) ∧
    -Real.log (1000 / 1381) ≤ (2582463 / 8000000) := by
  have h := checkLog_sound (w := (381 / 2381)) (n := 12)
    (lo := (161403937 / 500000000)) (hi := (2582463 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381 / 1000) = 1/(1000 / 1381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10875 : Bounds (161403937 / 500000000) (2582463 / 8000000) (Real.log (1381 / 1000)) := by
  have h := reflection_log_10875_neg
  have he : Real.log (1381 / 1000) = -Real.log (1000 / 1381) := by
    rw [show ((1381 / 1000) : ℝ) = ((1000 / 1381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10876_neg : (239825003 / 500000000) ≤ -Real.log (619 / 1000) ∧
    -Real.log (619 / 1000) ≤ (479650007 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 1619)) (n := 12)
    (lo := (239825003 / 500000000)) (hi := (479650007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 619) = 1/(619 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10876 : Bounds (-479650007 / 1000000000) (-239825003 / 500000000) (Real.log (619 / 1000)) := by
  have h := reflection_log_10876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10877_neg : (380927 / 1000000000) ≤ -Real.log (1000000 / 1000381) ∧
    -Real.log (1000000 / 1000381) ≤ (744 / 1953125) := by
  have h := checkLog_sound (w := (381 / 2000381)) (n := 12)
    (lo := (380927 / 1000000000)) (hi := (744 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000381 / 1000000) = 1/(1000000 / 1000381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10877 : Bounds (380927 / 1000000000) (744 / 1953125) (Real.log (1000381 / 1000000)) := by
  have h := reflection_log_10877_neg
  have he : Real.log (1000381 / 1000000) = -Real.log (1000000 / 1000381) := by
    rw [show ((1000381 / 1000000) : ℝ) = ((1000000 / 1000381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10878_neg : (23817 / 62500000) ≤ -Real.log (999619 / 1000000) ∧
    -Real.log (999619 / 1000000) ≤ (381073 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 1999619)) (n := 12)
    (lo := (23817 / 62500000)) (hi := (381073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999619) = 1/(999619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10878 : Bounds (-381073 / 1000000000) (-23817 / 62500000) (Real.log (999619 / 1000000)) := by
  have h := reflection_log_10878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10879_neg : (178133633 / 1000000000) ≤ -Real.log (200000 / 238997) ∧
    -Real.log (200000 / 238997) ≤ (89066817 / 500000000) := by
  have h := checkLog_sound (w := (38997 / 438997)) (n := 12)
    (lo := (178133633 / 1000000000)) (hi := (89066817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238997 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238997 / 200000) = 1/(200000 / 238997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10879 : Bounds (178133633 / 1000000000) (89066817 / 500000000) (Real.log (238997 / 200000)) := by
  have h := reflection_log_10879_neg
  have he : Real.log (238997 / 200000) = -Real.log (200000 / 238997) := by
    rw [show ((238997 / 200000) : ℝ) = ((200000 / 238997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0170 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10880_neg : (6777949 / 31250000) ≤ -Real.log (161003 / 200000) ∧
    -Real.log (161003 / 200000) ≤ (216894369 / 1000000000) := by
  have h := checkLog_sound (w := (38997 / 361003)) (n := 12)
    (lo := (6777949 / 31250000)) (hi := (216894369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161003) = 1/(161003 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10880 : Bounds (-216894369 / 1000000000) (-6777949 / 31250000) (Real.log (161003 / 200000)) := by
  have h := reflection_log_10880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10881_neg : (178897367 / 1000000000) ≤ -Real.log (500000 / 597949) ∧
    -Real.log (500000 / 597949) ≤ (22362171 / 125000000) := by
  have h := checkLog_sound (w := (97949 / 1097949)) (n := 12)
    (lo := (178897367 / 1000000000)) (hi := (22362171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597949 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597949 / 500000) = 1/(500000 / 597949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10881 : Bounds (178897367 / 1000000000) (22362171 / 125000000) (Real.log (597949 / 500000)) := by
  have h := reflection_log_10881_neg
  have he : Real.log (597949 / 500000) = -Real.log (500000 / 597949) := by
    rw [show ((597949 / 500000) : ℝ) = ((500000 / 597949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10882_neg : (6813411 / 31250000) ≤ -Real.log (402051 / 500000) ∧
    -Real.log (402051 / 500000) ≤ (218029153 / 1000000000) := by
  have h := checkLog_sound (w := (97949 / 902051)) (n := 12)
    (lo := (6813411 / 31250000)) (hi := (218029153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402051) = 1/(402051 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10882 : Bounds (-218029153 / 1000000000) (-6813411 / 31250000) (Real.log (402051 / 500000)) := by
  have h := reflection_log_10882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10883_neg : (4891473 / 125000000) ≤ -Real.log (240405993399 / 250000000000) ∧
    -Real.log (240405993399 / 250000000000) ≤ (7826357 / 200000000) := by
  have h := checkLog_sound (w := (9594006601 / 490405993399)) (n := 12)
    (lo := (4891473 / 125000000)) (hi := (7826357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240405993399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240405993399) = 1/(240405993399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10883 : Bounds (-7826357 / 200000000) (-4891473 / 125000000) (Real.log (240405993399 / 250000000000)) := by
  have h := reflection_log_10883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10884_neg : (7752147 / 200000000) ≤ -Real.log (38479233991 / 40000000000) ∧
    -Real.log (38479233991 / 40000000000) ≤ (1211273 / 31250000) := by
  have h := checkLog_sound (w := (1520766009 / 78479233991)) (n := 12)
    (lo := (7752147 / 200000000)) (hi := (1211273 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38479233991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38479233991) = 1/(38479233991 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10884 : Bounds (-1211273 / 31250000) (-7752147 / 200000000) (Real.log (38479233991 / 40000000000)) := by
  have h := reflection_log_10884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10885_neg : (395028001 / 1000000000) ≤ -Real.log (25000000000 / 37110643901) ∧
    -Real.log (25000000000 / 37110643901) ≤ (197514001 / 500000000) := by
  have h := checkLog_sound (w := (12110643901 / 62110643901)) (n := 12)
    (lo := (395028001 / 1000000000)) (hi := (197514001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37110643901 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37110643901 / 25000000000) = 1/(25000000000 / 37110643901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10885 : Bounds (395028001 / 1000000000) (197514001 / 500000000) (Real.log (37110643901 / 25000000000)) := by
  have h := reflection_log_10885_neg
  have he : Real.log (37110643901 / 25000000000) = -Real.log (25000000000 / 37110643901) := by
    rw [show ((37110643901 / 25000000000) : ℝ) = ((25000000000 / 37110643901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10886_neg : (396926519 / 1000000000) ≤ -Real.log (25000000000 / 37181166071) ∧
    -Real.log (25000000000 / 37181166071) ≤ (9923163 / 25000000) := by
  have h := checkLog_sound (w := (12181166071 / 62181166071)) (n := 12)
    (lo := (396926519 / 1000000000)) (hi := (9923163 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37181166071 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37181166071 / 25000000000) = 1/(25000000000 / 37181166071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10886 : Bounds (396926519 / 1000000000) (9923163 / 25000000) (Real.log (37181166071 / 25000000000)) := by
  have h := reflection_log_10886_neg
  have he : Real.log (37181166071 / 25000000000) = -Real.log (25000000000 / 37181166071) := by
    rw [show ((37181166071 / 25000000000) : ℝ) = ((25000000000 / 37181166071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10887_neg : (800119299 / 1000000000) ≤ -Real.log (250000000000 / 556451612903) ∧
    -Real.log (250000000000 / 556451612903) ≤ (800119301 / 1000000000) := by
  have h := checkLog_sound (w := (56451612903 / 1056451612903)) (n := 12)
    (lo := (106972119 / 1000000000)) (hi := (2674303 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556451612903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556451612903 / 500000000000) = 1/(250000000000 / 556451612903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10887 : Bounds (800119299 / 1000000000) (800119301 / 1000000000) (Real.log (556451612903 / 250000000000)) := by
  have h := reflection_log_10887_neg
  have he : Real.log (556451612903 / 250000000000) = -Real.log (250000000000 / 556451612903) := by
    rw [show ((556451612903 / 250000000000) : ℝ) = ((250000000000 / 556451612903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10888_neg : (20061447 / 25000000) ≤ -Real.log (500000000000 / 1115508885299) ∧
    -Real.log (500000000000 / 1115508885299) ≤ (401228941 / 500000000) := by
  have h := checkLog_sound (w := (115508885299 / 2115508885299)) (n := 12)
    (lo := (1093107 / 10000000)) (hi := (109310701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115508885299 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1115508885299 / 1000000000000) = 1/(500000000000 / 1115508885299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10888 : Bounds (20061447 / 25000000) (401228941 / 500000000) (Real.log (1115508885299 / 500000000000)) := by
  have h := reflection_log_10888_neg
  have he : Real.log (1115508885299 / 500000000000) = -Real.log (500000000000 / 1115508885299) := by
    rw [show ((1115508885299 / 500000000000) : ℝ) = ((500000000000 / 1115508885299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10889_neg : (12941269 / 40000000) ≤ -Real.log (500 / 691) ∧
    -Real.log (500 / 691) ≤ (161765863 / 500000000) := by
  have h := checkLog_sound (w := (191 / 1191)) (n := 12)
    (lo := (12941269 / 40000000)) (hi := (161765863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 500) = 1/(500 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10889 : Bounds (12941269 / 40000000) (161765863 / 500000000) (Real.log (691 / 500)) := by
  have h := reflection_log_10889_neg
  have he : Real.log (691 / 500) = -Real.log (500 / 691) := by
    rw [show ((691 / 500) : ℝ) = ((500 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10890_neg : (481266821 / 1000000000) ≤ -Real.log (309 / 500) ∧
    -Real.log (309 / 500) ≤ (240633411 / 500000000) := by
  have h := checkLog_sound (w := (191 / 809)) (n := 12)
    (lo := (481266821 / 1000000000)) (hi := (240633411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 309) = 1/(309 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10890 : Bounds (-240633411 / 500000000) (-481266821 / 1000000000) (Real.log (309 / 500)) := by
  have h := reflection_log_10890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10891_neg : (381927 / 1000000000) ≤ -Real.log (500000 / 500191) ∧
    -Real.log (500000 / 500191) ≤ (47741 / 125000000) := by
  have h := checkLog_sound (w := (191 / 1000191)) (n := 12)
    (lo := (381927 / 1000000000)) (hi := (47741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500191 / 500000) = 1/(500000 / 500191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10891 : Bounds (381927 / 1000000000) (47741 / 125000000) (Real.log (500191 / 500000)) := by
  have h := reflection_log_10891_neg
  have he : Real.log (500191 / 500000) = -Real.log (500000 / 500191) := by
    rw [show ((500191 / 500000) : ℝ) = ((500000 / 500191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10892_neg : (47759 / 125000000) ≤ -Real.log (499809 / 500000) ∧
    -Real.log (499809 / 500000) ≤ (382073 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 999809)) (n := 12)
    (lo := (47759 / 125000000)) (hi := (382073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499809) = 1/(499809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10892 : Bounds (-382073 / 1000000000) (-47759 / 125000000) (Real.log (499809 / 500000)) := by
  have h := reflection_log_10892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10893_neg : (44646773 / 250000000) ≤ -Real.log (1000000 / 1195527) ∧
    -Real.log (1000000 / 1195527) ≤ (178587093 / 1000000000) := by
  have h := checkLog_sound (w := (195527 / 2195527)) (n := 12)
    (lo := (44646773 / 250000000)) (hi := (178587093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195527 / 1000000) = 1/(1000000 / 1195527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10893 : Bounds (44646773 / 250000000) (178587093 / 1000000000) (Real.log (1195527 / 1000000)) := by
  have h := reflection_log_10893_neg
  have he : Real.log (1195527 / 1000000) = -Real.log (1000000 / 1195527) := by
    rw [show ((1195527 / 1000000) : ℝ) = ((1000000 / 1195527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10894_neg : (108783937 / 500000000) ≤ -Real.log (804473 / 1000000) ∧
    -Real.log (804473 / 1000000) ≤ (1740543 / 8000000) := by
  have h := checkLog_sound (w := (195527 / 1804473)) (n := 12)
    (lo := (108783937 / 500000000)) (hi := (1740543 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804473) = 1/(804473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10894 : Bounds (-1740543 / 8000000) (-108783937 / 500000000) (Real.log (804473 / 1000000)) := by
  have h := reflection_log_10894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10895_neg : (44837829 / 250000000) ≤ -Real.log (1000000 / 1196441) ∧
    -Real.log (1000000 / 1196441) ≤ (179351317 / 1000000000) := by
  have h := checkLog_sound (w := (196441 / 2196441)) (n := 12)
    (lo := (44837829 / 250000000)) (hi := (179351317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196441 / 1000000) = 1/(1000000 / 1196441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10895 : Bounds (44837829 / 250000000) (179351317 / 1000000000) (Real.log (1196441 / 1000000)) := by
  have h := reflection_log_10895_neg
  have he : Real.log (1196441 / 1000000) = -Real.log (1000000 / 1196441) := by
    rw [show ((1196441 / 1000000) : ℝ) = ((1000000 / 1196441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10896_neg : (218704667 / 1000000000) ≤ -Real.log (803559 / 1000000) ∧
    -Real.log (803559 / 1000000) ≤ (54676167 / 250000000) := by
  have h := checkLog_sound (w := (196441 / 1803559)) (n := 12)
    (lo := (218704667 / 1000000000)) (hi := (54676167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803559) = 1/(803559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10896 : Bounds (-54676167 / 250000000) (-218704667 / 1000000000) (Real.log (803559 / 1000000)) := by
  have h := reflection_log_10896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10897_neg : (39353351 / 1000000000) ≤ -Real.log (961410933519 / 1000000000000) ∧
    -Real.log (961410933519 / 1000000000000) ≤ (4919169 / 125000000) := by
  have h := checkLog_sound (w := (38589066481 / 1961410933519)) (n := 12)
    (lo := (39353351 / 1000000000)) (hi := (4919169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961410933519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961410933519) = 1/(961410933519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10897 : Bounds (-4919169 / 125000000) (-39353351 / 1000000000) (Real.log (961410933519 / 1000000000000)) := by
  have h := reflection_log_10897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10898_neg : (38980781 / 1000000000) ≤ -Real.log (961769192271 / 1000000000000) ∧
    -Real.log (961769192271 / 1000000000000) ≤ (19490391 / 500000000) := by
  have h := checkLog_sound (w := (38230807729 / 1961769192271)) (n := 12)
    (lo := (38980781 / 1000000000)) (hi := (19490391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961769192271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961769192271) = 1/(961769192271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10898 : Bounds (-19490391 / 500000000) (-38980781 / 1000000000) (Real.log (961769192271 / 1000000000000)) := by
  have h := reflection_log_10898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10899_neg : (198077483 / 500000000) ≤ -Real.log (500000000000 / 743049797817) ∧
    -Real.log (500000000000 / 743049797817) ≤ (396154967 / 1000000000) := by
  have h := checkLog_sound (w := (243049797817 / 1243049797817)) (n := 12)
    (lo := (198077483 / 500000000)) (hi := (396154967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743049797817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743049797817 / 500000000000) = 1/(500000000000 / 743049797817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10899 : Bounds (198077483 / 500000000) (396154967 / 1000000000) (Real.log (743049797817 / 500000000000)) := by
  have h := reflection_log_10899_neg
  have he : Real.log (743049797817 / 500000000000) = -Real.log (500000000000 / 743049797817) := by
    rw [show ((743049797817 / 500000000000) : ℝ) = ((500000000000 / 743049797817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10900_neg : (24878499 / 62500000) ≤ -Real.log (10000000000 / 14889273843) ∧
    -Real.log (10000000000 / 14889273843) ≤ (79611197 / 200000000) := by
  have h := checkLog_sound (w := (4889273843 / 24889273843)) (n := 12)
    (lo := (24878499 / 62500000)) (hi := (79611197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14889273843 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14889273843 / 10000000000) = 1/(10000000000 / 14889273843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10900 : Bounds (24878499 / 62500000) (79611197 / 200000000) (Real.log (14889273843 / 10000000000)) := by
  have h := reflection_log_10900_neg
  have he : Real.log (14889273843 / 10000000000) = -Real.log (10000000000 / 14889273843) := by
    rw [show ((14889273843 / 10000000000) : ℝ) = ((10000000000 / 14889273843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10901_neg : (20061447 / 25000000) ≤ -Real.log (250000000000 / 557754442649) ∧
    -Real.log (250000000000 / 557754442649) ≤ (401228941 / 500000000) := by
  have h := checkLog_sound (w := (57754442649 / 1057754442649)) (n := 12)
    (lo := (1093107 / 10000000)) (hi := (109310701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557754442649 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(557754442649 / 500000000000) = 1/(250000000000 / 557754442649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10901 : Bounds (20061447 / 25000000) (401228941 / 500000000) (Real.log (557754442649 / 250000000000)) := by
  have h := reflection_log_10901_neg
  have he : Real.log (557754442649 / 250000000000) = -Real.log (250000000000 / 557754442649) := by
    rw [show ((557754442649 / 250000000000) : ℝ) = ((250000000000 / 557754442649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10902_neg : (402399273 / 500000000) ≤ -Real.log (500000000000 / 1118122977347) ∧
    -Real.log (500000000000 / 1118122977347) ≤ (201199637 / 250000000) := by
  have h := checkLog_sound (w := (118122977347 / 2118122977347)) (n := 12)
    (lo := (55825683 / 500000000)) (hi := (111651367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118122977347 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1118122977347 / 1000000000000) = 1/(500000000000 / 1118122977347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10902 : Bounds (402399273 / 500000000) (201199637 / 250000000) (Real.log (1118122977347 / 500000000000)) := by
  have h := reflection_log_10902_neg
  have he : Real.log (1118122977347 / 500000000000) = -Real.log (500000000000 / 1118122977347) := by
    rw [show ((1118122977347 / 500000000000) : ℝ) = ((500000000000 / 1118122977347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10903_neg : (81063763 / 250000000) ≤ -Real.log (1000 / 1383) ∧
    -Real.log (1000 / 1383) ≤ (324255053 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2383)) (n := 12)
    (lo := (81063763 / 250000000)) (hi := (324255053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1383 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1383 / 1000) = 1/(1000 / 1383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10903 : Bounds (81063763 / 250000000) (324255053 / 1000000000) (Real.log (1383 / 1000)) := by
  have h := reflection_log_10903_neg
  have he : Real.log (1383 / 1000) = -Real.log (1000 / 1383) := by
    rw [show ((1383 / 1000) : ℝ) = ((1000 / 1383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10904_neg : (96577251 / 200000000) ≤ -Real.log (617 / 1000) ∧
    -Real.log (617 / 1000) ≤ (30180391 / 62500000) := by
  have h := checkLog_sound (w := (383 / 1617)) (n := 12)
    (lo := (96577251 / 200000000)) (hi := (30180391 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 617) = 1/(617 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10904 : Bounds (-30180391 / 62500000) (-96577251 / 200000000) (Real.log (617 / 1000)) := by
  have h := reflection_log_10904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10905_neg : (191463 / 500000000) ≤ -Real.log (1000000 / 1000383) ∧
    -Real.log (1000000 / 1000383) ≤ (382927 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2000383)) (n := 12)
    (lo := (191463 / 500000000)) (hi := (382927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000383 / 1000000) = 1/(1000000 / 1000383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10905 : Bounds (191463 / 500000000) (382927 / 1000000000) (Real.log (1000383 / 1000000)) := by
  have h := reflection_log_10905_neg
  have he : Real.log (1000383 / 1000000) = -Real.log (1000000 / 1000383) := by
    rw [show ((1000383 / 1000000) : ℝ) = ((1000000 / 1000383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10906_neg : (383073 / 1000000000) ≤ -Real.log (999617 / 1000000) ∧
    -Real.log (999617 / 1000000) ≤ (191537 / 500000000) := by
  have h := checkLog_sound (w := (383 / 1999617)) (n := 12)
    (lo := (383073 / 1000000000)) (hi := (191537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999617) = 1/(999617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10906 : Bounds (-191537 / 500000000) (-383073 / 1000000000) (Real.log (999617 / 1000000)) := by
  have h := reflection_log_10906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10907_neg : (89520173 / 500000000) ≤ -Real.log (1000000 / 1196069) ∧
    -Real.log (1000000 / 1196069) ≤ (179040347 / 1000000000) := by
  have h := checkLog_sound (w := (196069 / 2196069)) (n := 12)
    (lo := (89520173 / 500000000)) (hi := (179040347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196069 / 1000000) = 1/(1000000 / 1196069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10907 : Bounds (89520173 / 500000000) (179040347 / 1000000000) (Real.log (1196069 / 1000000)) := by
  have h := reflection_log_10907_neg
  have he : Real.log (1196069 / 1000000) = -Real.log (1000000 / 1196069) := by
    rw [show ((1196069 / 1000000) : ℝ) = ((1000000 / 1196069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10908_neg : (109120917 / 500000000) ≤ -Real.log (803931 / 1000000) ∧
    -Real.log (803931 / 1000000) ≤ (43648367 / 200000000) := by
  have h := checkLog_sound (w := (196069 / 1803931)) (n := 12)
    (lo := (109120917 / 500000000)) (hi := (43648367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803931) = 1/(803931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10908 : Bounds (-43648367 / 200000000) (-109120917 / 500000000) (Real.log (803931 / 1000000)) := by
  have h := reflection_log_10908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10909_neg : (179805059 / 1000000000) ≤ -Real.log (125000 / 149623) ∧
    -Real.log (125000 / 149623) ≤ (8990253 / 50000000) := by
  have h := checkLog_sound (w := (24623 / 274623)) (n := 12)
    (lo := (179805059 / 1000000000)) (hi := (8990253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149623 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149623 / 125000) = 1/(125000 / 149623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10909 : Bounds (179805059 / 1000000000) (8990253 / 50000000) (Real.log (149623 / 125000)) := by
  have h := reflection_log_10909_neg
  have he : Real.log (149623 / 125000) = -Real.log (125000 / 149623) := by
    rw [show ((149623 / 125000) : ℝ) = ((125000 / 149623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10910_neg : (219380639 / 1000000000) ≤ -Real.log (100377 / 125000) ∧
    -Real.log (100377 / 125000) ≤ (1371129 / 6250000) := by
  have h := checkLog_sound (w := (24623 / 225377)) (n := 12)
    (lo := (219380639 / 1000000000)) (hi := (1371129 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100377) = 1/(100377 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10910 : Bounds (-1371129 / 6250000) (-219380639 / 1000000000) (Real.log (100377 / 125000)) := by
  have h := reflection_log_10910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10911_neg : (1978779 / 50000000) ≤ -Real.log (15018707871 / 15625000000) ∧
    -Real.log (15018707871 / 15625000000) ≤ (39575581 / 1000000000) := by
  have h := checkLog_sound (w := (606292129 / 30643707871)) (n := 12)
    (lo := (1978779 / 50000000)) (hi := (39575581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15018707871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15018707871) = 1/(15018707871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10911 : Bounds (-39575581 / 1000000000) (-1978779 / 50000000) (Real.log (15018707871 / 15625000000)) := by
  have h := reflection_log_10911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10912_neg : (2450093 / 62500000) ≤ -Real.log (961556947239 / 1000000000000) ∧
    -Real.log (961556947239 / 1000000000000) ≤ (39201489 / 1000000000) := by
  have h := checkLog_sound (w := (38443052761 / 1961556947239)) (n := 12)
    (lo := (2450093 / 62500000)) (hi := (39201489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961556947239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961556947239) = 1/(961556947239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10912 : Bounds (-39201489 / 1000000000) (-2450093 / 62500000) (Real.log (961556947239 / 1000000000000)) := by
  have h := reflection_log_10912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10913_neg : (19864109 / 50000000) ≤ -Real.log (31250000000 / 46492990381) ∧
    -Real.log (31250000000 / 46492990381) ≤ (397282181 / 1000000000) := by
  have h := checkLog_sound (w := (15242990381 / 77742990381)) (n := 12)
    (lo := (19864109 / 50000000)) (hi := (397282181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46492990381 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46492990381 / 31250000000) = 1/(31250000000 / 46492990381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10913 : Bounds (19864109 / 50000000) (397282181 / 1000000000) (Real.log (46492990381 / 31250000000)) := by
  have h := reflection_log_10913_neg
  have he : Real.log (46492990381 / 31250000000) = -Real.log (31250000000 / 46492990381) := by
    rw [show ((46492990381 / 31250000000) : ℝ) = ((31250000000 / 46492990381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10914_neg : (399185699 / 1000000000) ≤ -Real.log (500000000000 / 745305199399) ∧
    -Real.log (500000000000 / 745305199399) ≤ (3991857 / 10000000) := by
  have h := checkLog_sound (w := (245305199399 / 1245305199399)) (n := 12)
    (lo := (399185699 / 1000000000)) (hi := (3991857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745305199399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745305199399 / 500000000000) = 1/(500000000000 / 745305199399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10914 : Bounds (399185699 / 1000000000) (3991857 / 10000000) (Real.log (745305199399 / 500000000000)) := by
  have h := reflection_log_10914_neg
  have he : Real.log (745305199399 / 500000000000) = -Real.log (500000000000 / 745305199399) := by
    rw [show ((745305199399 / 500000000000) : ℝ) = ((500000000000 / 745305199399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10915_neg : (402399273 / 500000000) ≤ -Real.log (250000000000 / 559061488673) ∧
    -Real.log (250000000000 / 559061488673) ≤ (201199637 / 250000000) := by
  have h := checkLog_sound (w := (59061488673 / 1059061488673)) (n := 12)
    (lo := (55825683 / 500000000)) (hi := (111651367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559061488673 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(559061488673 / 500000000000) = 1/(250000000000 / 559061488673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10915 : Bounds (402399273 / 500000000) (201199637 / 250000000) (Real.log (559061488673 / 250000000000)) := by
  have h := reflection_log_10915_neg
  have he : Real.log (559061488673 / 250000000000) = -Real.log (250000000000 / 559061488673) := by
    rw [show ((559061488673 / 250000000000) : ℝ) = ((250000000000 / 559061488673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10916_neg : (807141307 / 1000000000) ≤ -Real.log (10000000000 / 22414910859) ∧
    -Real.log (10000000000 / 22414910859) ≤ (807141309 / 1000000000) := by
  have h := checkLog_sound (w := (2414910859 / 42414910859)) (n := 12)
    (lo := (113994127 / 1000000000)) (hi := (7124633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22414910859 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(22414910859 / 20000000000) = 1/(10000000000 / 22414910859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10916 : Bounds (807141307 / 1000000000) (807141309 / 1000000000) (Real.log (22414910859 / 10000000000)) := by
  have h := reflection_log_10916_neg
  have he : Real.log (22414910859 / 10000000000) = -Real.log (10000000000 / 22414910859) := by
    rw [show ((22414910859 / 10000000000) : ℝ) = ((10000000000 / 22414910859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10917_neg : (324977857 / 1000000000) ≤ -Real.log (125 / 173) ∧
    -Real.log (125 / 173) ≤ (162488929 / 500000000) := by
  have h := checkLog_sound (w := (24 / 149)) (n := 12)
    (lo := (324977857 / 1000000000)) (hi := (162488929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173 / 125) = 1/(125 / 173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10917 : Bounds (324977857 / 1000000000) (162488929 / 500000000) (Real.log (173 / 125)) := by
  have h := reflection_log_10917_neg
  have he : Real.log (173 / 125) = -Real.log (125 / 173) := by
    rw [show ((173 / 125) : ℝ) = ((125 / 173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10918_neg : (96901663 / 200000000) ≤ -Real.log (77 / 125) ∧
    -Real.log (77 / 125) ≤ (121127079 / 250000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 77) = 1/(77 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10918 : Bounds (-121127079 / 250000000) (-96901663 / 200000000) (Real.log (77 / 125)) := by
  have h := reflection_log_10918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10919_neg : (191963 / 500000000) ≤ -Real.log (15625 / 15631) ∧
    -Real.log (15625 / 15631) ≤ (383927 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 15628)) (n := 12)
    (lo := (191963 / 500000000)) (hi := (383927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15631 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15631 / 15625) = 1/(15625 / 15631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10919 : Bounds (191963 / 500000000) (383927 / 1000000000) (Real.log (15631 / 15625)) := by
  have h := reflection_log_10919_neg
  have he : Real.log (15631 / 15625) = -Real.log (15625 / 15631) := by
    rw [show ((15631 / 15625) : ℝ) = ((15625 / 15631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10920_neg : (384073 / 1000000000) ≤ -Real.log (15619 / 15625) ∧
    -Real.log (15619 / 15625) ≤ (192037 / 500000000) := by
  have h := checkLog_sound (w := (3 / 15622)) (n := 12)
    (lo := (384073 / 1000000000)) (hi := (192037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15619) = 1/(15619 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10920 : Bounds (-192037 / 500000000) (-384073 / 1000000000) (Real.log (15619 / 15625)) := by
  have h := reflection_log_10920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10921_neg : (89746697 / 500000000) ≤ -Real.log (1000000 / 1196611) ∧
    -Real.log (1000000 / 1196611) ≤ (35898679 / 200000000) := by
  have h := checkLog_sound (w := (196611 / 2196611)) (n := 12)
    (lo := (89746697 / 500000000)) (hi := (35898679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196611 / 1000000) = 1/(1000000 / 1196611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10921 : Bounds (89746697 / 500000000) (35898679 / 200000000) (Real.log (1196611 / 1000000)) := by
  have h := reflection_log_10921_neg
  have he : Real.log (1196611 / 1000000) = -Real.log (1000000 / 1196611) := by
    rw [show ((1196611 / 1000000) : ℝ) = ((1000000 / 1196611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10922_neg : (27364531 / 125000000) ≤ -Real.log (803389 / 1000000) ∧
    -Real.log (803389 / 1000000) ≤ (218916249 / 1000000000) := by
  have h := checkLog_sound (w := (196611 / 1803389)) (n := 12)
    (lo := (27364531 / 125000000)) (hi := (218916249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803389) = 1/(803389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10922 : Bounds (-218916249 / 1000000000) (-27364531 / 125000000) (Real.log (803389 / 1000000)) := by
  have h := reflection_log_10922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10923_neg : (180258597 / 1000000000) ≤ -Real.log (1000000 / 1197527) ∧
    -Real.log (1000000 / 1197527) ≤ (90129299 / 500000000) := by
  have h := checkLog_sound (w := (197527 / 2197527)) (n := 12)
    (lo := (180258597 / 1000000000)) (hi := (90129299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197527 / 1000000) = 1/(1000000 / 1197527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10923 : Bounds (180258597 / 1000000000) (90129299 / 500000000) (Real.log (1197527 / 1000000)) := by
  have h := reflection_log_10923_neg
  have he : Real.log (1197527 / 1000000) = -Real.log (1000000 / 1197527) := by
    rw [show ((1197527 / 1000000) : ℝ) = ((1000000 / 1197527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10924_neg : (220057069 / 1000000000) ≤ -Real.log (802473 / 1000000) ∧
    -Real.log (802473 / 1000000) ≤ (22005707 / 100000000) := by
  have h := checkLog_sound (w := (197527 / 1802473)) (n := 12)
    (lo := (220057069 / 1000000000)) (hi := (22005707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802473) = 1/(802473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10924 : Bounds (-22005707 / 100000000) (-220057069 / 1000000000) (Real.log (802473 / 1000000)) := by
  have h := reflection_log_10924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10925_neg : (4974809 / 125000000) ≤ -Real.log (960983084271 / 1000000000000) ∧
    -Real.log (960983084271 / 1000000000000) ≤ (39798473 / 1000000000) := by
  have h := checkLog_sound (w := (39016915729 / 1960983084271)) (n := 12)
    (lo := (4974809 / 125000000)) (hi := (39798473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960983084271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960983084271) = 1/(960983084271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10925 : Bounds (-39798473 / 1000000000) (-4974809 / 125000000) (Real.log (960983084271 / 1000000000000)) := by
  have h := reflection_log_10925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10926_neg : (19711427 / 500000000) ≤ -Real.log (961344114679 / 1000000000000) ∧
    -Real.log (961344114679 / 1000000000000) ≤ (7884571 / 200000000) := by
  have h := checkLog_sound (w := (38655885321 / 1961344114679)) (n := 12)
    (lo := (19711427 / 500000000)) (hi := (7884571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961344114679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961344114679) = 1/(961344114679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10926 : Bounds (-7884571 / 200000000) (-19711427 / 500000000) (Real.log (961344114679 / 1000000000000)) := by
  have h := reflection_log_10926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10927_neg : (398409643 / 1000000000) ≤ -Real.log (500000000000 / 744727025139) ∧
    -Real.log (500000000000 / 744727025139) ≤ (99602411 / 250000000) := by
  have h := checkLog_sound (w := (244727025139 / 1244727025139)) (n := 12)
    (lo := (398409643 / 1000000000)) (hi := (99602411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744727025139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744727025139 / 500000000000) = 1/(500000000000 / 744727025139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10927 : Bounds (398409643 / 1000000000) (99602411 / 250000000) (Real.log (744727025139 / 500000000000)) := by
  have h := reflection_log_10927_neg
  have he : Real.log (744727025139 / 500000000000) = -Real.log (500000000000 / 744727025139) := by
    rw [show ((744727025139 / 500000000000) : ℝ) = ((500000000000 / 744727025139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10928_neg : (200157833 / 500000000) ≤ -Real.log (500000000000 / 746147845473) ∧
    -Real.log (500000000000 / 746147845473) ≤ (400315667 / 1000000000) := by
  have h := checkLog_sound (w := (246147845473 / 1246147845473)) (n := 12)
    (lo := (200157833 / 500000000)) (hi := (400315667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746147845473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746147845473 / 500000000000) = 1/(500000000000 / 746147845473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10928 : Bounds (200157833 / 500000000) (400315667 / 1000000000) (Real.log (746147845473 / 500000000000)) := by
  have h := reflection_log_10928_neg
  have he : Real.log (746147845473 / 500000000000) = -Real.log (500000000000 / 746147845473) := by
    rw [show ((746147845473 / 500000000000) : ℝ) = ((500000000000 / 746147845473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10929_neg : (807141307 / 1000000000) ≤ -Real.log (500000000000 / 1120745542949) ∧
    -Real.log (500000000000 / 1120745542949) ≤ (807141309 / 1000000000) := by
  have h := checkLog_sound (w := (120745542949 / 2120745542949)) (n := 12)
    (lo := (113994127 / 1000000000)) (hi := (7124633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120745542949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120745542949 / 1000000000000) = 1/(500000000000 / 1120745542949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10929 : Bounds (807141307 / 1000000000) (807141309 / 1000000000) (Real.log (1120745542949 / 500000000000)) := by
  have h := reflection_log_10929_neg
  have he : Real.log (1120745542949 / 500000000000) = -Real.log (500000000000 / 1120745542949) := by
    rw [show ((1120745542949 / 500000000000) : ℝ) = ((500000000000 / 1120745542949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10930_neg : (202371543 / 250000000) ≤ -Real.log (500000000000 / 1123376623377) ∧
    -Real.log (500000000000 / 1123376623377) ≤ (404743087 / 500000000) := by
  have h := checkLog_sound (w := (123376623377 / 2123376623377)) (n := 12)
    (lo := (7271187 / 62500000)) (hi := (116338993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123376623377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123376623377 / 1000000000000) = 1/(500000000000 / 1123376623377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10930 : Bounds (202371543 / 250000000) (404743087 / 500000000) (Real.log (1123376623377 / 500000000000)) := by
  have h := reflection_log_10930_neg
  have he : Real.log (1123376623377 / 500000000000) = -Real.log (500000000000 / 1123376623377) := by
    rw [show ((1123376623377 / 500000000000) : ℝ) = ((500000000000 / 1123376623377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10931_neg : (325700139 / 1000000000) ≤ -Real.log (200 / 277) ∧
    -Real.log (200 / 277) ≤ (16285007 / 50000000) := by
  have h := checkLog_sound (w := (77 / 477)) (n := 12)
    (lo := (325700139 / 1000000000)) (hi := (16285007 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277 / 200) = 1/(200 / 277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10931 : Bounds (325700139 / 1000000000) (16285007 / 50000000) (Real.log (277 / 200)) := by
  have h := reflection_log_10931_neg
  have he : Real.log (277 / 200) = -Real.log (200 / 277) := by
    rw [show ((277 / 200) : ℝ) = ((200 / 277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10932_neg : (486133011 / 1000000000) ≤ -Real.log (123 / 200) ∧
    -Real.log (123 / 200) ≤ (121533253 / 250000000) := by
  have h := checkLog_sound (w := (77 / 323)) (n := 12)
    (lo := (486133011 / 1000000000)) (hi := (121533253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 123) = 1/(123 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10932 : Bounds (-121533253 / 250000000) (-486133011 / 1000000000) (Real.log (123 / 200)) := by
  have h := reflection_log_10932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10933_neg : (15397 / 40000000) ≤ -Real.log (200000 / 200077) ∧
    -Real.log (200000 / 200077) ≤ (192463 / 500000000) := by
  have h := checkLog_sound (w := (77 / 400077)) (n := 12)
    (lo := (15397 / 40000000)) (hi := (192463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200077 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200077 / 200000) = 1/(200000 / 200077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10933 : Bounds (15397 / 40000000) (192463 / 500000000) (Real.log (200077 / 200000)) := by
  have h := reflection_log_10933_neg
  have he : Real.log (200077 / 200000) = -Real.log (200000 / 200077) := by
    rw [show ((200077 / 200000) : ℝ) = ((200000 / 200077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10934_neg : (192537 / 500000000) ≤ -Real.log (199923 / 200000) ∧
    -Real.log (199923 / 200000) ≤ (15403 / 40000000) := by
  have h := checkLog_sound (w := (77 / 399923)) (n := 12)
    (lo := (192537 / 500000000)) (hi := (15403 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199923) = 1/(199923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10934 : Bounds (-15403 / 40000000) (-192537 / 500000000) (Real.log (199923 / 200000)) := by
  have h := reflection_log_10934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10935_neg : (179947073 / 1000000000) ≤ -Real.log (500000 / 598577) ∧
    -Real.log (500000 / 598577) ≤ (89973537 / 500000000) := by
  have h := checkLog_sound (w := (98577 / 1098577)) (n := 12)
    (lo := (179947073 / 1000000000)) (hi := (89973537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598577 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598577 / 500000) = 1/(500000 / 598577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10935 : Bounds (179947073 / 1000000000) (89973537 / 500000000) (Real.log (598577 / 500000)) := by
  have h := reflection_log_10935_neg
  have he : Real.log (598577 / 500000) = -Real.log (500000 / 598577) := by
    rw [show ((598577 / 500000) : ℝ) = ((500000 / 598577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10936_neg : (54898091 / 250000000) ≤ -Real.log (401423 / 500000) ∧
    -Real.log (401423 / 500000) ≤ (43918473 / 200000000) := by
  have h := checkLog_sound (w := (98577 / 901423)) (n := 12)
    (lo := (54898091 / 250000000)) (hi := (43918473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401423) = 1/(401423 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10936 : Bounds (-43918473 / 200000000) (-54898091 / 250000000) (Real.log (401423 / 500000)) := by
  have h := reflection_log_10936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10937_neg : (180712763 / 1000000000) ≤ -Real.log (1000000 / 1198071) ∧
    -Real.log (1000000 / 1198071) ≤ (45178191 / 250000000) := by
  have h := checkLog_sound (w := (198071 / 2198071)) (n := 12)
    (lo := (180712763 / 1000000000)) (hi := (45178191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198071 / 1000000) = 1/(1000000 / 1198071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10937 : Bounds (180712763 / 1000000000) (45178191 / 250000000) (Real.log (1198071 / 1000000)) := by
  have h := reflection_log_10937_neg
  have he : Real.log (1198071 / 1000000) = -Real.log (1000000 / 1198071) := by
    rw [show ((1198071 / 1000000) : ℝ) = ((1000000 / 1198071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10938_neg : (220735203 / 1000000000) ≤ -Real.log (801929 / 1000000) ∧
    -Real.log (801929 / 1000000) ≤ (55183801 / 250000000) := by
  have h := checkLog_sound (w := (198071 / 1801929)) (n := 12)
    (lo := (220735203 / 1000000000)) (hi := (55183801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801929) = 1/(801929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10938 : Bounds (-55183801 / 250000000) (-220735203 / 1000000000) (Real.log (801929 / 1000000)) := by
  have h := reflection_log_10938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10939_neg : (1000561 / 25000000) ≤ -Real.log (960767878959 / 1000000000000) ∧
    -Real.log (960767878959 / 1000000000000) ≤ (40022441 / 1000000000) := by
  have h := checkLog_sound (w := (39232121041 / 1960767878959)) (n := 12)
    (lo := (1000561 / 25000000)) (hi := (40022441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960767878959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960767878959) = 1/(960767878959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10939 : Bounds (-40022441 / 1000000000) (-1000561 / 25000000) (Real.log (960767878959 / 1000000000000)) := by
  have h := reflection_log_10939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10940_neg : (3964529 / 100000000) ≤ -Real.log (240282575071 / 250000000000) ∧
    -Real.log (240282575071 / 250000000000) ≤ (39645291 / 1000000000) := by
  have h := checkLog_sound (w := (9717424929 / 490282575071)) (n := 12)
    (lo := (3964529 / 100000000)) (hi := (39645291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240282575071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240282575071) = 1/(240282575071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10940 : Bounds (-39645291 / 1000000000) (-3964529 / 100000000) (Real.log (240282575071 / 250000000000)) := by
  have h := reflection_log_10940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10941_neg : (399539437 / 1000000000) ≤ -Real.log (250000000000 / 372784444339) ∧
    -Real.log (250000000000 / 372784444339) ≤ (199769719 / 500000000) := by
  have h := checkLog_sound (w := (122784444339 / 622784444339)) (n := 12)
    (lo := (399539437 / 1000000000)) (hi := (199769719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372784444339 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372784444339 / 250000000000) = 1/(250000000000 / 372784444339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10941 : Bounds (399539437 / 1000000000) (199769719 / 500000000) (Real.log (372784444339 / 250000000000)) := by
  have h := reflection_log_10941_neg
  have he : Real.log (372784444339 / 250000000000) = -Real.log (250000000000 / 372784444339) := by
    rw [show ((372784444339 / 250000000000) : ℝ) = ((250000000000 / 372784444339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10942_neg : (401447967 / 1000000000) ≤ -Real.log (500000000000 / 746993187677) ∧
    -Real.log (500000000000 / 746993187677) ≤ (12545249 / 31250000) := by
  have h := checkLog_sound (w := (246993187677 / 1246993187677)) (n := 12)
    (lo := (401447967 / 1000000000)) (hi := (12545249 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746993187677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746993187677 / 500000000000) = 1/(500000000000 / 746993187677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10942 : Bounds (401447967 / 1000000000) (12545249 / 31250000) (Real.log (746993187677 / 500000000000)) := by
  have h := reflection_log_10942_neg
  have he : Real.log (746993187677 / 500000000000) = -Real.log (500000000000 / 746993187677) := by
    rw [show ((746993187677 / 500000000000) : ℝ) = ((500000000000 / 746993187677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10943_neg : (202371543 / 250000000) ≤ -Real.log (31250000000 / 70211038961) ∧
    -Real.log (31250000000 / 70211038961) ≤ (404743087 / 500000000) := by
  have h := checkLog_sound (w := (7711038961 / 132711038961)) (n := 12)
    (lo := (7271187 / 62500000)) (hi := (116338993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70211038961 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70211038961 / 62500000000) = 1/(31250000000 / 70211038961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10943 : Bounds (202371543 / 250000000) (404743087 / 500000000) (Real.log (70211038961 / 31250000000)) := by
  have h := reflection_log_10943_neg
  have he : Real.log (70211038961 / 31250000000) = -Real.log (31250000000 / 70211038961) := by
    rw [show ((70211038961 / 31250000000) : ℝ) = ((31250000000 / 70211038961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0171 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10944_neg : (16236663 / 20000000) ≤ -Real.log (500000000000 / 1126016260163) ∧
    -Real.log (500000000000 / 1126016260163) ≤ (12684893 / 15625000) := by
  have h := checkLog_sound (w := (126016260163 / 2126016260163)) (n := 12)
    (lo := (11868597 / 100000000)) (hi := (118685971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126016260163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126016260163 / 1000000000000) = 1/(500000000000 / 1126016260163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10944 : Bounds (16236663 / 20000000) (12684893 / 15625000) (Real.log (1126016260163 / 500000000000)) := by
  have h := reflection_log_10944_neg
  have he : Real.log (1126016260163 / 500000000000) = -Real.log (500000000000 / 1126016260163) := by
    rw [show ((1126016260163 / 500000000000) : ℝ) = ((500000000000 / 1126016260163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10945_neg : (3264219 / 10000000) ≤ -Real.log (500 / 693) ∧
    -Real.log (500 / 693) ≤ (326421901 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1193)) (n := 12)
    (lo := (3264219 / 10000000)) (hi := (326421901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 500) = 1/(500 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10945 : Bounds (3264219 / 10000000) (326421901 / 1000000000) (Real.log (693 / 500)) := by
  have h := reflection_log_10945_neg
  have he : Real.log (693 / 500) = -Real.log (500 / 693) := by
    rw [show ((693 / 500) : ℝ) = ((500 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10946_neg : (9755207 / 20000000) ≤ -Real.log (307 / 500) ∧
    -Real.log (307 / 500) ≤ (487760351 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 807)) (n := 12)
    (lo := (9755207 / 20000000)) (hi := (487760351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 307) = 1/(307 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10946 : Bounds (-487760351 / 1000000000) (-9755207 / 20000000) (Real.log (307 / 500)) := by
  have h := reflection_log_10946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10947_neg : (15437 / 40000000) ≤ -Real.log (500000 / 500193) ∧
    -Real.log (500000 / 500193) ≤ (192963 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1000193)) (n := 12)
    (lo := (15437 / 40000000)) (hi := (192963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500193 / 500000) = 1/(500000 / 500193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10947 : Bounds (15437 / 40000000) (192963 / 500000000) (Real.log (500193 / 500000)) := by
  have h := reflection_log_10947_neg
  have he : Real.log (500193 / 500000) = -Real.log (500000 / 500193) := by
    rw [show ((500193 / 500000) : ℝ) = ((500000 / 500193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10948_neg : (193037 / 500000000) ≤ -Real.log (499807 / 500000) ∧
    -Real.log (499807 / 500000) ≤ (15443 / 40000000) := by
  have h := checkLog_sound (w := (193 / 999807)) (n := 12)
    (lo := (193037 / 500000000)) (hi := (15443 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499807) = 1/(499807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10948 : Bounds (-15443 / 40000000) (-193037 / 500000000) (Real.log (499807 / 500000)) := by
  have h := reflection_log_10948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10949_neg : (180399711 / 1000000000) ≤ -Real.log (15625 / 18714) ∧
    -Real.log (15625 / 18714) ≤ (5637491 / 31250000) := by
  have h := checkLog_sound (w := (3089 / 34339)) (n := 12)
    (lo := (180399711 / 1000000000)) (hi := (5637491 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18714 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18714 / 15625) = 1/(15625 / 18714) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10949 : Bounds (180399711 / 1000000000) (5637491 / 31250000) (Real.log (18714 / 15625)) := by
  have h := reflection_log_10949_neg
  have he : Real.log (18714 / 15625) = -Real.log (15625 / 18714) := by
    rw [show ((18714 / 15625) : ℝ) = ((15625 / 18714) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10950_neg : (22026769 / 100000000) ≤ -Real.log (12536 / 15625) ∧
    -Real.log (12536 / 15625) ≤ (220267691 / 1000000000) := by
  have h := checkLog_sound (w := (3089 / 28161)) (n := 12)
    (lo := (22026769 / 100000000)) (hi := (220267691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12536) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12536) = 1/(12536 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10950 : Bounds (-220267691 / 1000000000) (-22026769 / 100000000) (Real.log (12536 / 15625)) := by
  have h := reflection_log_10950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10951_neg : (181166723 / 1000000000) ≤ -Real.log (200000 / 239723) ∧
    -Real.log (200000 / 239723) ≤ (45291681 / 250000000) := by
  have h := checkLog_sound (w := (39723 / 439723)) (n := 12)
    (lo := (181166723 / 1000000000)) (hi := (45291681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239723 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239723 / 200000) = 1/(200000 / 239723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10951 : Bounds (181166723 / 1000000000) (45291681 / 250000000) (Real.log (239723 / 200000)) := by
  have h := reflection_log_10951_neg
  have he : Real.log (239723 / 200000) = -Real.log (200000 / 239723) := by
    rw [show ((239723 / 200000) : ℝ) = ((200000 / 239723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10952_neg : (110706899 / 500000000) ≤ -Real.log (160277 / 200000) ∧
    -Real.log (160277 / 200000) ≤ (221413799 / 1000000000) := by
  have h := checkLog_sound (w := (39723 / 360277)) (n := 12)
    (lo := (110706899 / 500000000)) (hi := (221413799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160277) = 1/(160277 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10952 : Bounds (-221413799 / 1000000000) (-110706899 / 500000000) (Real.log (160277 / 200000)) := by
  have h := reflection_log_10952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10953_neg : (20123537 / 500000000) ≤ -Real.log (38422083271 / 40000000000) ∧
    -Real.log (38422083271 / 40000000000) ≤ (1609883 / 40000000) := by
  have h := checkLog_sound (w := (1577916729 / 78422083271)) (n := 12)
    (lo := (20123537 / 500000000)) (hi := (1609883 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38422083271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38422083271) = 1/(38422083271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10953 : Bounds (-1609883 / 40000000) (-20123537 / 500000000) (Real.log (38422083271 / 40000000000)) := by
  have h := reflection_log_10953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10954_neg : (39867979 / 1000000000) ≤ -Real.log (234598704 / 244140625) ∧
    -Real.log (234598704 / 244140625) ≤ (1993399 / 50000000) := by
  have h := checkLog_sound (w := (9541921 / 478739329)) (n := 12)
    (lo := (39867979 / 1000000000)) (hi := (1993399 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 234598704) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 234598704) = 1/(234598704 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10954 : Bounds (-1993399 / 50000000) (-39867979 / 1000000000) (Real.log (234598704 / 244140625)) := by
  have h := reflection_log_10954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10955_neg : (400667401 / 1000000000) ≤ -Real.log (20000000000 / 29856413529) ∧
    -Real.log (20000000000 / 29856413529) ≤ (200333701 / 500000000) := by
  have h := checkLog_sound (w := (9856413529 / 49856413529)) (n := 12)
    (lo := (400667401 / 1000000000)) (hi := (200333701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29856413529 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29856413529 / 20000000000) = 1/(20000000000 / 29856413529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10955 : Bounds (400667401 / 1000000000) (200333701 / 500000000) (Real.log (29856413529 / 20000000000)) := by
  have h := reflection_log_10955_neg
  have he : Real.log (29856413529 / 20000000000) = -Real.log (20000000000 / 29856413529) := by
    rw [show ((29856413529 / 20000000000) : ℝ) = ((20000000000 / 29856413529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10956_neg : (402580521 / 1000000000) ≤ -Real.log (500000000000 / 747839677559) ∧
    -Real.log (500000000000 / 747839677559) ≤ (201290261 / 500000000) := by
  have h := checkLog_sound (w := (247839677559 / 1247839677559)) (n := 12)
    (lo := (402580521 / 1000000000)) (hi := (201290261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747839677559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747839677559 / 500000000000) = 1/(500000000000 / 747839677559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10956 : Bounds (402580521 / 1000000000) (201290261 / 500000000) (Real.log (747839677559 / 500000000000)) := by
  have h := reflection_log_10956_neg
  have he : Real.log (747839677559 / 500000000000) = -Real.log (500000000000 / 747839677559) := by
    rw [show ((747839677559 / 500000000000) : ℝ) = ((500000000000 / 747839677559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10957_neg : (16236663 / 20000000) ≤ -Real.log (250000000000 / 563008130081) ∧
    -Real.log (250000000000 / 563008130081) ≤ (12684893 / 15625000) := by
  have h := checkLog_sound (w := (63008130081 / 1063008130081)) (n := 12)
    (lo := (11868597 / 100000000)) (hi := (118685971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563008130081 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563008130081 / 500000000000) = 1/(250000000000 / 563008130081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10957 : Bounds (16236663 / 20000000) (12684893 / 15625000) (Real.log (563008130081 / 250000000000)) := by
  have h := reflection_log_10957_neg
  have he : Real.log (563008130081 / 250000000000) = -Real.log (250000000000 / 563008130081) := by
    rw [show ((563008130081 / 250000000000) : ℝ) = ((250000000000 / 563008130081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10958_neg : (814182251 / 1000000000) ≤ -Real.log (100000000000 / 225732899023) ∧
    -Real.log (100000000000 / 225732899023) ≤ (814182253 / 1000000000) := by
  have h := checkLog_sound (w := (25732899023 / 425732899023)) (n := 12)
    (lo := (121035071 / 1000000000)) (hi := (1891173 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225732899023 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225732899023 / 200000000000) = 1/(100000000000 / 225732899023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10958 : Bounds (814182251 / 1000000000) (814182253 / 1000000000) (Real.log (225732899023 / 100000000000)) := by
  have h := reflection_log_10958_neg
  have he : Real.log (225732899023 / 100000000000) = -Real.log (100000000000 / 225732899023) := by
    rw [show ((225732899023 / 100000000000) : ℝ) = ((100000000000 / 225732899023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10959_neg : (327143141 / 1000000000) ≤ -Real.log (1000 / 1387) ∧
    -Real.log (1000 / 1387) ≤ (163571571 / 500000000) := by
  have h := checkLog_sound (w := (387 / 2387)) (n := 12)
    (lo := (327143141 / 1000000000)) (hi := (163571571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1387 / 1000) = 1/(1000 / 1387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10959 : Bounds (327143141 / 1000000000) (163571571 / 500000000) (Real.log (1387 / 1000)) := by
  have h := reflection_log_10959_neg
  have he : Real.log (1387 / 1000) = -Real.log (1000 / 1387) := by
    rw [show ((1387 / 1000) : ℝ) = ((1000 / 1387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10960_neg : (489390343 / 1000000000) ≤ -Real.log (613 / 1000) ∧
    -Real.log (613 / 1000) ≤ (61173793 / 125000000) := by
  have h := checkLog_sound (w := (387 / 1613)) (n := 12)
    (lo := (489390343 / 1000000000)) (hi := (61173793 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 613) = 1/(613 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10960 : Bounds (-61173793 / 125000000) (-489390343 / 1000000000) (Real.log (613 / 1000)) := by
  have h := reflection_log_10960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10961_neg : (15477 / 40000000) ≤ -Real.log (1000000 / 1000387) ∧
    -Real.log (1000000 / 1000387) ≤ (193463 / 500000000) := by
  have h := checkLog_sound (w := (387 / 2000387)) (n := 12)
    (lo := (15477 / 40000000)) (hi := (193463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000387 / 1000000) = 1/(1000000 / 1000387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10961 : Bounds (15477 / 40000000) (193463 / 500000000) (Real.log (1000387 / 1000000)) := by
  have h := reflection_log_10961_neg
  have he : Real.log (1000387 / 1000000) = -Real.log (1000000 / 1000387) := by
    rw [show ((1000387 / 1000000) : ℝ) = ((1000000 / 1000387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10962_neg : (193537 / 500000000) ≤ -Real.log (999613 / 1000000) ∧
    -Real.log (999613 / 1000000) ≤ (15483 / 40000000) := by
  have h := checkLog_sound (w := (387 / 1999613)) (n := 12)
    (lo := (193537 / 500000000)) (hi := (15483 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999613) = 1/(999613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10962 : Bounds (-15483 / 40000000) (-193537 / 500000000) (Real.log (999613 / 1000000)) := by
  have h := reflection_log_10962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10963_neg : (90426489 / 500000000) ≤ -Real.log (1000000 / 1198239) ∧
    -Real.log (1000000 / 1198239) ≤ (180852979 / 1000000000) := by
  have h := checkLog_sound (w := (198239 / 2198239)) (n := 12)
    (lo := (90426489 / 500000000)) (hi := (180852979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198239 / 1000000) = 1/(1000000 / 1198239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10963 : Bounds (90426489 / 500000000) (180852979 / 1000000000) (Real.log (1198239 / 1000000)) := by
  have h := reflection_log_10963_neg
  have he : Real.log (1198239 / 1000000) = -Real.log (1000000 / 1198239) := by
    rw [show ((1198239 / 1000000) : ℝ) = ((1000000 / 1198239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10964_neg : (2761809 / 12500000) ≤ -Real.log (801761 / 1000000) ∧
    -Real.log (801761 / 1000000) ≤ (220944721 / 1000000000) := by
  have h := checkLog_sound (w := (198239 / 1801761)) (n := 12)
    (lo := (2761809 / 12500000)) (hi := (220944721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801761) = 1/(801761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10964 : Bounds (-220944721 / 1000000000) (-2761809 / 12500000) (Real.log (801761 / 1000000)) := by
  have h := reflection_log_10964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10965_neg : (181620477 / 1000000000) ≤ -Real.log (1000000 / 1199159) ∧
    -Real.log (1000000 / 1199159) ≤ (90810239 / 500000000) := by
  have h := checkLog_sound (w := (199159 / 2199159)) (n := 12)
    (lo := (181620477 / 1000000000)) (hi := (90810239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199159 / 1000000) = 1/(1000000 / 1199159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10965 : Bounds (181620477 / 1000000000) (90810239 / 500000000) (Real.log (1199159 / 1000000)) := by
  have h := reflection_log_10965_neg
  have he : Real.log (1199159 / 1000000) = -Real.log (1000000 / 1199159) := by
    rw [show ((1199159 / 1000000) : ℝ) = ((1000000 / 1199159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10966_neg : (222092853 / 1000000000) ≤ -Real.log (800841 / 1000000) ∧
    -Real.log (800841 / 1000000) ≤ (111046427 / 500000000) := by
  have h := checkLog_sound (w := (199159 / 1800841)) (n := 12)
    (lo := (222092853 / 1000000000)) (hi := (111046427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800841) = 1/(800841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10966 : Bounds (-111046427 / 500000000) (-222092853 / 1000000000) (Real.log (800841 / 1000000)) := by
  have h := reflection_log_10966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10967_neg : (323779 / 8000000) ≤ -Real.log (960335692719 / 1000000000000) ∧
    -Real.log (960335692719 / 1000000000000) ≤ (5059047 / 125000000) := by
  have h := checkLog_sound (w := (39664307281 / 1960335692719)) (n := 12)
    (lo := (323779 / 8000000)) (hi := (5059047 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960335692719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960335692719) = 1/(960335692719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10967 : Bounds (-5059047 / 125000000) (-323779 / 8000000) (Real.log (960335692719 / 1000000000000)) := by
  have h := reflection_log_10967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10968_neg : (40091741 / 1000000000) ≤ -Real.log (960701298879 / 1000000000000) ∧
    -Real.log (960701298879 / 1000000000000) ≤ (20045871 / 500000000) := by
  have h := checkLog_sound (w := (39298701121 / 1960701298879)) (n := 12)
    (lo := (40091741 / 1000000000)) (hi := (20045871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960701298879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960701298879) = 1/(960701298879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10968 : Bounds (-20045871 / 500000000) (-40091741 / 1000000000) (Real.log (960701298879 / 1000000000000)) := by
  have h := reflection_log_10968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10969_neg : (401797699 / 1000000000) ≤ -Real.log (500000000000 / 747254481073) ∧
    -Real.log (500000000000 / 747254481073) ≤ (4017977 / 10000000) := by
  have h := checkLog_sound (w := (247254481073 / 1247254481073)) (n := 12)
    (lo := (401797699 / 1000000000)) (hi := (4017977 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747254481073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747254481073 / 500000000000) = 1/(500000000000 / 747254481073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10969 : Bounds (401797699 / 1000000000) (4017977 / 10000000) (Real.log (747254481073 / 500000000000)) := by
  have h := reflection_log_10969_neg
  have he : Real.log (747254481073 / 500000000000) = -Real.log (500000000000 / 747254481073) := by
    rw [show ((747254481073 / 500000000000) : ℝ) = ((500000000000 / 747254481073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10970_neg : (403713331 / 1000000000) ≤ -Real.log (250000000000 / 374343658729) ∧
    -Real.log (250000000000 / 374343658729) ≤ (100928333 / 250000000) := by
  have h := checkLog_sound (w := (124343658729 / 624343658729)) (n := 12)
    (lo := (403713331 / 1000000000)) (hi := (100928333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374343658729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374343658729 / 250000000000) = 1/(250000000000 / 374343658729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10970 : Bounds (403713331 / 1000000000) (100928333 / 250000000) (Real.log (374343658729 / 250000000000)) := by
  have h := reflection_log_10970_neg
  have he : Real.log (374343658729 / 250000000000) = -Real.log (250000000000 / 374343658729) := by
    rw [show ((374343658729 / 250000000000) : ℝ) = ((250000000000 / 374343658729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10971_neg : (814182251 / 1000000000) ≤ -Real.log (250000000000 / 564332247557) ∧
    -Real.log (250000000000 / 564332247557) ≤ (814182253 / 1000000000) := by
  have h := checkLog_sound (w := (64332247557 / 1064332247557)) (n := 12)
    (lo := (121035071 / 1000000000)) (hi := (1891173 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564332247557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(564332247557 / 500000000000) = 1/(250000000000 / 564332247557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10971 : Bounds (814182251 / 1000000000) (814182253 / 1000000000) (Real.log (564332247557 / 250000000000)) := by
  have h := reflection_log_10971_neg
  have he : Real.log (564332247557 / 250000000000) = -Real.log (250000000000 / 564332247557) := by
    rw [show ((564332247557 / 250000000000) : ℝ) = ((250000000000 / 564332247557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10972_neg : (816533483 / 1000000000) ≤ -Real.log (50000000000 / 113132137031) ∧
    -Real.log (50000000000 / 113132137031) ≤ (163306697 / 200000000) := by
  have h := checkLog_sound (w := (13132137031 / 213132137031)) (n := 12)
    (lo := (123386303 / 1000000000)) (hi := (1927911 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113132137031 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113132137031 / 100000000000) = 1/(50000000000 / 113132137031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10972 : Bounds (816533483 / 1000000000) (163306697 / 200000000) (Real.log (113132137031 / 50000000000)) := by
  have h := reflection_log_10972_neg
  have he : Real.log (113132137031 / 50000000000) = -Real.log (50000000000 / 113132137031) := by
    rw [show ((113132137031 / 50000000000) : ℝ) = ((50000000000 / 113132137031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10973_neg : (163931931 / 500000000) ≤ -Real.log (250 / 347) ∧
    -Real.log (250 / 347) ≤ (327863863 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 597)) (n := 12)
    (lo := (163931931 / 500000000)) (hi := (327863863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 250) = 1/(250 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10973 : Bounds (163931931 / 500000000) (327863863 / 1000000000) (Real.log (347 / 250)) := by
  have h := reflection_log_10973_neg
  have he : Real.log (347 / 250) = -Real.log (250 / 347) := by
    rw [show ((347 / 250) : ℝ) = ((250 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10974_neg : (122755749 / 250000000) ≤ -Real.log (153 / 250) ∧
    -Real.log (153 / 250) ≤ (491022997 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 403)) (n := 12)
    (lo := (122755749 / 250000000)) (hi := (491022997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 153) = 1/(153 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10974 : Bounds (-491022997 / 1000000000) (-122755749 / 250000000) (Real.log (153 / 250)) := by
  have h := reflection_log_10974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10975_neg : (96981 / 250000000) ≤ -Real.log (250000 / 250097) ∧
    -Real.log (250000 / 250097) ≤ (15517 / 40000000) := by
  have h := checkLog_sound (w := (97 / 500097)) (n := 12)
    (lo := (96981 / 250000000)) (hi := (15517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250097 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250097 / 250000) = 1/(250000 / 250097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10975 : Bounds (96981 / 250000000) (15517 / 40000000) (Real.log (250097 / 250000)) := by
  have h := reflection_log_10975_neg
  have he : Real.log (250097 / 250000) = -Real.log (250000 / 250097) := by
    rw [show ((250097 / 250000) : ℝ) = ((250000 / 250097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10976_neg : (15523 / 40000000) ≤ -Real.log (249903 / 250000) ∧
    -Real.log (249903 / 250000) ≤ (97019 / 250000000) := by
  have h := checkLog_sound (w := (97 / 499903)) (n := 12)
    (lo := (15523 / 40000000)) (hi := (97019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249903) = 1/(249903 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10976 : Bounds (-97019 / 250000000) (-15523 / 40000000) (Real.log (249903 / 250000)) := by
  have h := reflection_log_10976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10977_neg : (181306041 / 1000000000) ≤ -Real.log (500000 / 599391) ∧
    -Real.log (500000 / 599391) ≤ (90653021 / 500000000) := by
  have h := checkLog_sound (w := (99391 / 1099391)) (n := 12)
    (lo := (181306041 / 1000000000)) (hi := (90653021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599391 / 500000) = 1/(500000 / 599391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10977 : Bounds (181306041 / 1000000000) (90653021 / 500000000) (Real.log (599391 / 500000)) := by
  have h := reflection_log_10977_neg
  have he : Real.log (599391 / 500000) = -Real.log (500000 / 599391) := by
    rw [show ((599391 / 500000) : ℝ) = ((500000 / 599391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10978_neg : (221622209 / 1000000000) ≤ -Real.log (400609 / 500000) ∧
    -Real.log (400609 / 500000) ≤ (22162221 / 100000000) := by
  have h := checkLog_sound (w := (99391 / 900609)) (n := 12)
    (lo := (221622209 / 1000000000)) (hi := (22162221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400609) = 1/(400609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10978 : Bounds (-22162221 / 100000000) (-221622209 / 1000000000) (Real.log (400609 / 500000)) := by
  have h := reflection_log_10978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10979_neg : (91037013 / 500000000) ≤ -Real.log (1000000 / 1199703) ∧
    -Real.log (1000000 / 1199703) ≤ (182074027 / 1000000000) := by
  have h := checkLog_sound (w := (199703 / 2199703)) (n := 12)
    (lo := (91037013 / 500000000)) (hi := (182074027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199703 / 1000000) = 1/(1000000 / 1199703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10979 : Bounds (91037013 / 500000000) (182074027 / 1000000000) (Real.log (1199703 / 1000000)) := by
  have h := reflection_log_10979_neg
  have he : Real.log (1199703 / 1000000) = -Real.log (1000000 / 1199703) := by
    rw [show ((1199703 / 1000000) : ℝ) = ((1000000 / 1199703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10980_neg : (22277237 / 100000000) ≤ -Real.log (800297 / 1000000) ∧
    -Real.log (800297 / 1000000) ≤ (222772371 / 1000000000) := by
  have h := checkLog_sound (w := (199703 / 1800297)) (n := 12)
    (lo := (22277237 / 100000000)) (hi := (222772371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800297) = 1/(800297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10980 : Bounds (-222772371 / 1000000000) (-22277237 / 100000000) (Real.log (800297 / 1000000)) := by
  have h := reflection_log_10980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10981_neg : (5087293 / 125000000) ≤ -Real.log (960118711791 / 1000000000000) ∧
    -Real.log (960118711791 / 1000000000000) ≤ (8139669 / 200000000) := by
  have h := checkLog_sound (w := (39881288209 / 1960118711791)) (n := 12)
    (lo := (5087293 / 125000000)) (hi := (8139669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960118711791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960118711791) = 1/(960118711791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10981 : Bounds (-8139669 / 200000000) (-5087293 / 125000000) (Real.log (960118711791 / 1000000000000)) := by
  have h := reflection_log_10981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10982_neg : (40316167 / 1000000000) ≤ -Real.log (240121429119 / 250000000000) ∧
    -Real.log (240121429119 / 250000000000) ≤ (5039521 / 125000000) := by
  have h := checkLog_sound (w := (9878570881 / 490121429119)) (n := 12)
    (lo := (40316167 / 1000000000)) (hi := (5039521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240121429119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240121429119) = 1/(240121429119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10982 : Bounds (-5039521 / 125000000) (-40316167 / 1000000000) (Real.log (240121429119 / 250000000000)) := by
  have h := reflection_log_10982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10983_neg : (1611713 / 4000000) ≤ -Real.log (500000000000 / 748099768103) ∧
    -Real.log (500000000000 / 748099768103) ≤ (402928251 / 1000000000) := by
  have h := checkLog_sound (w := (248099768103 / 1248099768103)) (n := 12)
    (lo := (1611713 / 4000000)) (hi := (402928251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748099768103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748099768103 / 500000000000) = 1/(500000000000 / 748099768103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10983 : Bounds (1611713 / 4000000) (402928251 / 1000000000) (Real.log (748099768103 / 500000000000)) := by
  have h := reflection_log_10983_neg
  have he : Real.log (748099768103 / 500000000000) = -Real.log (500000000000 / 748099768103) := by
    rw [show ((748099768103 / 500000000000) : ℝ) = ((500000000000 / 748099768103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10984_neg : (101211599 / 250000000) ≤ -Real.log (12500000000 / 18738402743) ∧
    -Real.log (12500000000 / 18738402743) ≤ (404846397 / 1000000000) := by
  have h := checkLog_sound (w := (6238402743 / 31238402743)) (n := 12)
    (lo := (101211599 / 250000000)) (hi := (404846397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18738402743 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18738402743 / 12500000000) = 1/(12500000000 / 18738402743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10984 : Bounds (101211599 / 250000000) (404846397 / 1000000000) (Real.log (18738402743 / 12500000000)) := by
  have h := reflection_log_10984_neg
  have he : Real.log (18738402743 / 12500000000) = -Real.log (12500000000 / 18738402743) := by
    rw [show ((18738402743 / 12500000000) : ℝ) = ((12500000000 / 18738402743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10985_neg : (816533483 / 1000000000) ≤ -Real.log (500000000000 / 1131321370309) ∧
    -Real.log (500000000000 / 1131321370309) ≤ (163306697 / 200000000) := by
  have h := checkLog_sound (w := (131321370309 / 2131321370309)) (n := 12)
    (lo := (123386303 / 1000000000)) (hi := (1927911 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131321370309 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131321370309 / 1000000000000) = 1/(500000000000 / 1131321370309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10985 : Bounds (816533483 / 1000000000) (163306697 / 200000000) (Real.log (1131321370309 / 500000000000)) := by
  have h := reflection_log_10985_neg
  have he : Real.log (1131321370309 / 500000000000) = -Real.log (500000000000 / 1131321370309) := by
    rw [show ((1131321370309 / 500000000000) : ℝ) = ((500000000000 / 1131321370309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10986_neg : (818886857 / 1000000000) ≤ -Real.log (100000000000 / 226797385621) ∧
    -Real.log (100000000000 / 226797385621) ≤ (818886859 / 1000000000) := by
  have h := checkLog_sound (w := (26797385621 / 426797385621)) (n := 12)
    (lo := (125739677 / 1000000000)) (hi := (62869839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226797385621 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226797385621 / 200000000000) = 1/(100000000000 / 226797385621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10986 : Bounds (818886857 / 1000000000) (818886859 / 1000000000) (Real.log (226797385621 / 100000000000)) := by
  have h := reflection_log_10986_neg
  have he : Real.log (226797385621 / 100000000000) = -Real.log (100000000000 / 226797385621) := by
    rw [show ((226797385621 / 100000000000) : ℝ) = ((100000000000 / 226797385621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10987_neg : (328584063 / 1000000000) ≤ -Real.log (1000 / 1389) ∧
    -Real.log (1000 / 1389) ≤ (2567063 / 7812500) := by
  have h := checkLog_sound (w := (389 / 2389)) (n := 12)
    (lo := (328584063 / 1000000000)) (hi := (2567063 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389 / 1000) = 1/(1000 / 1389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10987 : Bounds (328584063 / 1000000000) (2567063 / 7812500) (Real.log (1389 / 1000)) := by
  have h := reflection_log_10987_neg
  have he : Real.log (1389 / 1000) = -Real.log (1000 / 1389) := by
    rw [show ((1389 / 1000) : ℝ) = ((1000 / 1389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10988_neg : (492658319 / 1000000000) ≤ -Real.log (611 / 1000) ∧
    -Real.log (611 / 1000) ≤ (6158229 / 12500000) := by
  have h := checkLog_sound (w := (389 / 1611)) (n := 12)
    (lo := (492658319 / 1000000000)) (hi := (6158229 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 611) = 1/(611 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10988 : Bounds (-6158229 / 12500000) (-492658319 / 1000000000) (Real.log (611 / 1000)) := by
  have h := reflection_log_10988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10989_neg : (97231 / 250000000) ≤ -Real.log (1000000 / 1000389) ∧
    -Real.log (1000000 / 1000389) ≤ (15557 / 40000000) := by
  have h := checkLog_sound (w := (389 / 2000389)) (n := 12)
    (lo := (97231 / 250000000)) (hi := (15557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000389 / 1000000) = 1/(1000000 / 1000389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10989 : Bounds (97231 / 250000000) (15557 / 40000000) (Real.log (1000389 / 1000000)) := by
  have h := reflection_log_10989_neg
  have he : Real.log (1000389 / 1000000) = -Real.log (1000000 / 1000389) := by
    rw [show ((1000389 / 1000000) : ℝ) = ((1000000 / 1000389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10990_neg : (15563 / 40000000) ≤ -Real.log (999611 / 1000000) ∧
    -Real.log (999611 / 1000000) ≤ (97269 / 250000000) := by
  have h := checkLog_sound (w := (389 / 1999611)) (n := 12)
    (lo := (15563 / 40000000)) (hi := (97269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999611) = 1/(999611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10990 : Bounds (-97269 / 250000000) (-15563 / 40000000) (Real.log (999611 / 1000000)) := by
  have h := reflection_log_10990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10991_neg : (45439933 / 250000000) ≤ -Real.log (500000 / 599663) ∧
    -Real.log (500000 / 599663) ≤ (181759733 / 1000000000) := by
  have h := checkLog_sound (w := (99663 / 1099663)) (n := 12)
    (lo := (45439933 / 250000000)) (hi := (181759733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599663 / 500000) = 1/(500000 / 599663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10991 : Bounds (45439933 / 250000000) (181759733 / 1000000000) (Real.log (599663 / 500000)) := by
  have h := reflection_log_10991_neg
  have he : Real.log (599663 / 500000) = -Real.log (500000 / 599663) := by
    rw [show ((599663 / 500000) : ℝ) = ((500000 / 599663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10992_neg : (111150703 / 500000000) ≤ -Real.log (400337 / 500000) ∧
    -Real.log (400337 / 500000) ≤ (222301407 / 1000000000) := by
  have h := checkLog_sound (w := (99663 / 900337)) (n := 12)
    (lo := (111150703 / 500000000)) (hi := (222301407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400337) = 1/(400337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10992 : Bounds (-222301407 / 1000000000) (-111150703 / 500000000) (Real.log (400337 / 500000)) := by
  have h := reflection_log_10992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10993_neg : (91264101 / 500000000) ≤ -Real.log (125000 / 150031) ∧
    -Real.log (125000 / 150031) ≤ (182528203 / 1000000000) := by
  have h := checkLog_sound (w := (25031 / 275031)) (n := 12)
    (lo := (91264101 / 500000000)) (hi := (182528203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150031 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150031 / 125000) = 1/(125000 / 150031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10993 : Bounds (91264101 / 500000000) (182528203 / 1000000000) (Real.log (150031 / 125000)) := by
  have h := reflection_log_10993_neg
  have he : Real.log (150031 / 125000) = -Real.log (125000 / 150031) := by
    rw [show ((150031 / 125000) : ℝ) = ((125000 / 150031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10994_neg : (223453599 / 1000000000) ≤ -Real.log (99969 / 125000) ∧
    -Real.log (99969 / 125000) ≤ (279317 / 1250000) := by
  have h := checkLog_sound (w := (25031 / 224969)) (n := 12)
    (lo := (223453599 / 1000000000)) (hi := (279317 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99969) = 1/(99969 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10994 : Bounds (-279317 / 1250000) (-223453599 / 1000000000) (Real.log (99969 / 125000)) := by
  have h := reflection_log_10994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10995_neg : (40925397 / 1000000000) ≤ -Real.log (14998449039 / 15625000000) ∧
    -Real.log (14998449039 / 15625000000) ≤ (20462699 / 500000000) := by
  have h := checkLog_sound (w := (626550961 / 30623449039)) (n := 12)
    (lo := (40925397 / 1000000000)) (hi := (20462699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14998449039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14998449039) = 1/(14998449039 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10995 : Bounds (-20462699 / 500000000) (-40925397 / 1000000000) (Real.log (14998449039 / 15625000000)) := by
  have h := reflection_log_10995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10996_neg : (40541673 / 1000000000) ≤ -Real.log (240067286431 / 250000000000) ∧
    -Real.log (240067286431 / 250000000000) ≤ (20270837 / 500000000) := by
  have h := checkLog_sound (w := (9932713569 / 490067286431)) (n := 12)
    (lo := (40541673 / 1000000000)) (hi := (20270837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240067286431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240067286431) = 1/(240067286431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10996 : Bounds (-20270837 / 500000000) (-40541673 / 1000000000) (Real.log (240067286431 / 250000000000)) := by
  have h := reflection_log_10996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10997_neg : (202030569 / 500000000) ≤ -Real.log (50000000000 / 74894776151) ∧
    -Real.log (50000000000 / 74894776151) ≤ (404061139 / 1000000000) := by
  have h := checkLog_sound (w := (24894776151 / 124894776151)) (n := 12)
    (lo := (202030569 / 500000000)) (hi := (404061139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74894776151 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74894776151 / 50000000000) = 1/(50000000000 / 74894776151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10997 : Bounds (202030569 / 500000000) (404061139 / 1000000000) (Real.log (74894776151 / 50000000000)) := by
  have h := reflection_log_10997_neg
  have he : Real.log (74894776151 / 50000000000) = -Real.log (50000000000 / 74894776151) := by
    rw [show ((74894776151 / 50000000000) : ℝ) = ((50000000000 / 74894776151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10998_neg : (405981801 / 1000000000) ≤ -Real.log (500000000000 / 750387620163) ∧
    -Real.log (500000000000 / 750387620163) ≤ (202990901 / 500000000) := by
  have h := checkLog_sound (w := (250387620163 / 1250387620163)) (n := 12)
    (lo := (405981801 / 1000000000)) (hi := (202990901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750387620163 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750387620163 / 500000000000) = 1/(500000000000 / 750387620163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10998 : Bounds (405981801 / 1000000000) (202990901 / 500000000) (Real.log (750387620163 / 500000000000)) := by
  have h := reflection_log_10998_neg
  have he : Real.log (750387620163 / 500000000000) = -Real.log (500000000000 / 750387620163) := by
    rw [show ((750387620163 / 500000000000) : ℝ) = ((500000000000 / 750387620163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10999_neg : (818886857 / 1000000000) ≤ -Real.log (62500000000 / 141748366013) ∧
    -Real.log (62500000000 / 141748366013) ≤ (818886859 / 1000000000) := by
  have h := checkLog_sound (w := (16748366013 / 266748366013)) (n := 12)
    (lo := (125739677 / 1000000000)) (hi := (62869839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141748366013 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(141748366013 / 125000000000) = 1/(62500000000 / 141748366013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10999 : Bounds (818886857 / 1000000000) (818886859 / 1000000000) (Real.log (141748366013 / 62500000000)) := by
  have h := reflection_log_10999_neg
  have he : Real.log (141748366013 / 62500000000) = -Real.log (62500000000 / 141748366013) := by
    rw [show ((141748366013 / 62500000000) : ℝ) = ((62500000000 / 141748366013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11000_neg : (821242383 / 1000000000) ≤ -Real.log (50000000000 / 113666121113) ∧
    -Real.log (50000000000 / 113666121113) ≤ (164248477 / 200000000) := by
  have h := checkLog_sound (w := (13666121113 / 213666121113)) (n := 12)
    (lo := (128095203 / 1000000000)) (hi := (32023801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113666121113 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113666121113 / 100000000000) = 1/(50000000000 / 113666121113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11000 : Bounds (821242383 / 1000000000) (164248477 / 200000000) (Real.log (113666121113 / 50000000000)) := by
  have h := reflection_log_11000_neg
  have he : Real.log (113666121113 / 50000000000) = -Real.log (50000000000 / 113666121113) := by
    rw [show ((113666121113 / 50000000000) : ℝ) = ((50000000000 / 113666121113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11001_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11001 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_11001_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11002_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11002 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_11002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11003_neg : (389923 / 1000000000) ≤ -Real.log (100000 / 100039) ∧
    -Real.log (100000 / 100039) ≤ (97481 / 250000000) := by
  have h := checkLog_sound (w := (39 / 200039)) (n := 12)
    (lo := (389923 / 1000000000)) (hi := (97481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100039 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100039 / 100000) = 1/(100000 / 100039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11003 : Bounds (389923 / 1000000000) (97481 / 250000000) (Real.log (100039 / 100000)) := by
  have h := reflection_log_11003_neg
  have he : Real.log (100039 / 100000) = -Real.log (100000 / 100039) := by
    rw [show ((100039 / 100000) : ℝ) = ((100000 / 100039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11004_neg : (97519 / 250000000) ≤ -Real.log (99961 / 100000) ∧
    -Real.log (99961 / 100000) ≤ (390077 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 199961)) (n := 12)
    (lo := (97519 / 250000000)) (hi := (390077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99961) = 1/(99961 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11004 : Bounds (-390077 / 1000000000) (-97519 / 250000000) (Real.log (99961 / 100000)) := by
  have h := reflection_log_11004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11005_neg : (182213217 / 1000000000) ≤ -Real.log (100000 / 119987) ∧
    -Real.log (100000 / 119987) ≤ (91106609 / 500000000) := by
  have h := checkLog_sound (w := (19987 / 219987)) (n := 12)
    (lo := (182213217 / 1000000000)) (hi := (91106609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119987 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119987 / 100000) = 1/(100000 / 119987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11005 : Bounds (182213217 / 1000000000) (91106609 / 500000000) (Real.log (119987 / 100000)) := by
  have h := reflection_log_11005_neg
  have he : Real.log (119987 / 100000) = -Real.log (100000 / 119987) := by
    rw [show ((119987 / 100000) : ℝ) = ((100000 / 119987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11006_neg : (27872633 / 125000000) ≤ -Real.log (80013 / 100000) ∧
    -Real.log (80013 / 100000) ≤ (44596213 / 200000000) := by
  have h := checkLog_sound (w := (19987 / 180013)) (n := 12)
    (lo := (27872633 / 125000000)) (hi := (44596213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80013) = 1/(80013 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11006 : Bounds (-44596213 / 200000000) (-27872633 / 125000000) (Real.log (80013 / 100000)) := by
  have h := reflection_log_11006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11007_neg : (182982171 / 1000000000) ≤ -Real.log (1000000 / 1200793) ∧
    -Real.log (1000000 / 1200793) ≤ (45745543 / 250000000) := by
  have h := checkLog_sound (w := (200793 / 2200793)) (n := 12)
    (lo := (182982171 / 1000000000)) (hi := (45745543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200793 / 1000000) = 1/(1000000 / 1200793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11007 : Bounds (182982171 / 1000000000) (45745543 / 250000000) (Real.log (1200793 / 1000000)) := by
  have h := reflection_log_11007_neg
  have he : Real.log (1200793 / 1000000) = -Real.log (1000000 / 1200793) := by
    rw [show ((1200793 / 1000000) : ℝ) = ((1000000 / 1200793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


