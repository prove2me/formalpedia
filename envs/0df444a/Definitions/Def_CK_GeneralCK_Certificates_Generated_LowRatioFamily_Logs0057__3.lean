-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0057__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0057__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:09:38.144696+00:00
-- url     : https://prove2.me/theorems/b9ef8b9e-0c3a-4a86-b96b-cf63eaf28b94
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0057 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0058, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0057 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0058, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0059)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0057 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0058, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0059)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0057 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0058, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0059) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0057 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0058, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0059).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0057 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3648_neg : (7864867 / 1000000000) ≤ -Real.log (9921659799 / 10000000000) ∧
    -Real.log (9921659799 / 10000000000) ≤ (1966217 / 250000000) := by
  have h := checkLog_sound (w := (78340201 / 19921659799)) (n := 12)
    (lo := (7864867 / 1000000000)) (hi := (1966217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9921659799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9921659799) = 1/(9921659799 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3648 : Bounds (-1966217 / 250000000) (-7864867 / 1000000000) (Real.log (9921659799 / 10000000000)) := by
  have h := reflection_log_3648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3649_neg : (44371111 / 250000000) ≤ -Real.log (500000000000 / 597104740589) ∧
    -Real.log (500000000000 / 597104740589) ≤ (35496889 / 200000000) := by
  have h := checkLog_sound (w := (97104740589 / 1097104740589)) (n := 12)
    (lo := (44371111 / 250000000)) (hi := (35496889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597104740589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597104740589 / 500000000000) = 1/(500000000000 / 597104740589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3649 : Bounds (44371111 / 250000000) (35496889 / 200000000) (Real.log (597104740589 / 500000000000)) := by
  have h := reflection_log_3649_neg
  have he : Real.log (597104740589 / 500000000000) = -Real.log (500000000000 / 597104740589) := by
    rw [show ((597104740589 / 500000000000) : ℝ) = ((500000000000 / 597104740589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3650_neg : (88971019 / 500000000) ≤ -Real.log (250000000000 / 298689017331) ∧
    -Real.log (250000000000 / 298689017331) ≤ (177942039 / 1000000000) := by
  have h := checkLog_sound (w := (48689017331 / 548689017331)) (n := 12)
    (lo := (88971019 / 500000000)) (hi := (177942039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298689017331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298689017331 / 250000000000) = 1/(250000000000 / 298689017331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3650 : Bounds (88971019 / 500000000) (177942039 / 1000000000) (Real.log (298689017331 / 250000000000)) := by
  have h := reflection_log_3650_neg
  have he : Real.log (298689017331 / 250000000000) = -Real.log (250000000000 / 298689017331) := by
    rw [show ((298689017331 / 250000000000) : ℝ) = ((250000000000 / 298689017331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3651_neg : (890291 / 2500000) ≤ -Real.log (31250000000 / 44617929109) ∧
    -Real.log (31250000000 / 44617929109) ≤ (356116401 / 1000000000) := by
  have h := checkLog_sound (w := (13367929109 / 75867929109)) (n := 12)
    (lo := (890291 / 2500000)) (hi := (356116401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44617929109 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44617929109 / 31250000000) = 1/(31250000000 / 44617929109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3651 : Bounds (890291 / 2500000) (356116401 / 1000000000) (Real.log (44617929109 / 31250000000)) := by
  have h := reflection_log_3651_neg
  have he : Real.log (44617929109 / 31250000000) = -Real.log (31250000000 / 44617929109) := by
    rw [show ((44617929109 / 31250000000) : ℝ) = ((31250000000 / 44617929109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3652_neg : (89080703 / 250000000) ≤ -Real.log (250000000000 / 357017117883) ∧
    -Real.log (250000000000 / 357017117883) ≤ (356322813 / 1000000000) := by
  have h := checkLog_sound (w := (107017117883 / 607017117883)) (n := 12)
    (lo := (89080703 / 250000000)) (hi := (356322813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357017117883 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357017117883 / 250000000000) = 1/(250000000000 / 357017117883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3652 : Bounds (89080703 / 250000000) (356322813 / 1000000000) (Real.log (357017117883 / 250000000000)) := by
  have h := reflection_log_3652_neg
  have he : Real.log (357017117883 / 250000000000) = -Real.log (250000000000 / 357017117883) := by
    rw [show ((357017117883 / 250000000000) : ℝ) = ((250000000000 / 357017117883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3653_neg : (162458927 / 1000000000) ≤ -Real.log (2500 / 2941) ∧
    -Real.log (2500 / 2941) ≤ (10153683 / 62500000) := by
  have h := checkLog_sound (w := (441 / 5441)) (n := 12)
    (lo := (162458927 / 1000000000)) (hi := (10153683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2941 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2941 / 2500) = 1/(2500 / 2941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3653 : Bounds (162458927 / 1000000000) (10153683 / 62500000) (Real.log (2941 / 2500)) := by
  have h := reflection_log_3653_neg
  have he : Real.log (2941 / 2500) = -Real.log (2500 / 2941) := by
    rw [show ((2941 / 2500) : ℝ) = ((2500 / 2941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3654_neg : (194070303 / 1000000000) ≤ -Real.log (2059 / 2500) ∧
    -Real.log (2059 / 2500) ≤ (6064697 / 31250000) := by
  have h := checkLog_sound (w := (441 / 4559)) (n := 12)
    (lo := (194070303 / 1000000000)) (hi := (6064697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2059) = 1/(2059 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3654 : Bounds (-6064697 / 31250000) (-194070303 / 1000000000) (Real.log (2059 / 2500)) := by
  have h := reflection_log_3654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3655_neg : (689 / 3906250) ≤ -Real.log (2500000 / 2500441) ∧
    -Real.log (2500000 / 2500441) ≤ (35277 / 200000000) := by
  have h := checkLog_sound (w := (441 / 5000441)) (n := 12)
    (lo := (689 / 3906250)) (hi := (35277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500441 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500441 / 2500000) = 1/(2500000 / 2500441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3655 : Bounds (689 / 3906250) (35277 / 200000000) (Real.log (2500441 / 2500000)) := by
  have h := reflection_log_3655_neg
  have he : Real.log (2500441 / 2500000) = -Real.log (2500000 / 2500441) := by
    rw [show ((2500441 / 2500000) : ℝ) = ((2500000 / 2500441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3656_neg : (35283 / 200000000) ≤ -Real.log (2499559 / 2500000) ∧
    -Real.log (2499559 / 2500000) ≤ (5513 / 31250000) := by
  have h := checkLog_sound (w := (441 / 4999559)) (n := 12)
    (lo := (35283 / 200000000)) (hi := (5513 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499559) = 1/(2499559 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3656 : Bounds (-5513 / 31250000) (-35283 / 200000000) (Real.log (2499559 / 2500000)) := by
  have h := reflection_log_3656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3657_neg : (84855721 / 1000000000) ≤ -Real.log (12500 / 13607) ∧
    -Real.log (12500 / 13607) ≤ (42427861 / 500000000) := by
  have h := checkLog_sound (w := (1107 / 26107)) (n := 12)
    (lo := (84855721 / 1000000000)) (hi := (42427861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13607 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13607 / 12500) = 1/(12500 / 13607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3657 : Bounds (84855721 / 1000000000) (42427861 / 500000000) (Real.log (13607 / 12500)) := by
  have h := reflection_log_3657_neg
  have he : Real.log (13607 / 12500) = -Real.log (12500 / 13607) := by
    rw [show ((13607 / 12500) : ℝ) = ((12500 / 13607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3658_neg : (11591189 / 125000000) ≤ -Real.log (11393 / 12500) ∧
    -Real.log (11393 / 12500) ≤ (92729513 / 1000000000) := by
  have h := checkLog_sound (w := (1107 / 23893)) (n := 12)
    (lo := (11591189 / 125000000)) (hi := (92729513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11393) = 1/(11393 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3658 : Bounds (-92729513 / 1000000000) (-11591189 / 125000000) (Real.log (11393 / 12500)) := by
  have h := reflection_log_3658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3659_neg : (1701303 / 20000000) ≤ -Real.log (250000 / 272197) ∧
    -Real.log (250000 / 272197) ≤ (85065151 / 1000000000) := by
  have h := checkLog_sound (w := (22197 / 522197)) (n := 12)
    (lo := (1701303 / 20000000)) (hi := (85065151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272197 / 250000) = 1/(250000 / 272197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3659 : Bounds (1701303 / 20000000) (85065151 / 1000000000) (Real.log (272197 / 250000)) := by
  have h := reflection_log_3659_neg
  have he : Real.log (272197 / 250000) = -Real.log (250000 / 272197) := by
    rw [show ((272197 / 250000) : ℝ) = ((250000 / 272197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3660_neg : (92979697 / 1000000000) ≤ -Real.log (227803 / 250000) ∧
    -Real.log (227803 / 250000) ≤ (46489849 / 500000000) := by
  have h := checkLog_sound (w := (22197 / 477803)) (n := 12)
    (lo := (92979697 / 1000000000)) (hi := (46489849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227803) = 1/(227803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3660 : Bounds (-46489849 / 500000000) (-92979697 / 1000000000) (Real.log (227803 / 250000)) := by
  have h := reflection_log_3660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3661_neg : (3957273 / 500000000) ≤ -Real.log (62007293191 / 62500000000) ∧
    -Real.log (62007293191 / 62500000000) ≤ (7914547 / 1000000000) := by
  have h := checkLog_sound (w := (492706809 / 124507293191)) (n := 12)
    (lo := (3957273 / 500000000)) (hi := (7914547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62007293191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62007293191) = 1/(62007293191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3661 : Bounds (-7914547 / 1000000000) (-3957273 / 500000000) (Real.log (62007293191 / 62500000000)) := by
  have h := reflection_log_3661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3662_neg : (787379 / 100000000) ≤ -Real.log (155024551 / 156250000) ∧
    -Real.log (155024551 / 156250000) ≤ (7873791 / 1000000000) := by
  have h := checkLog_sound (w := (1225449 / 311274551)) (n := 12)
    (lo := (787379 / 100000000)) (hi := (7873791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 155024551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 155024551) = 1/(155024551 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3662 : Bounds (-7873791 / 1000000000) (-787379 / 100000000) (Real.log (155024551 / 156250000)) := by
  have h := reflection_log_3662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3663_neg : (88792617 / 500000000) ≤ -Real.log (500000000000 / 597164925831) ∧
    -Real.log (500000000000 / 597164925831) ≤ (35517047 / 200000000) := by
  have h := checkLog_sound (w := (97164925831 / 1097164925831)) (n := 12)
    (lo := (88792617 / 500000000)) (hi := (35517047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597164925831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597164925831 / 500000000000) = 1/(500000000000 / 597164925831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3663 : Bounds (88792617 / 500000000) (35517047 / 200000000) (Real.log (597164925831 / 500000000000)) := by
  have h := reflection_log_3663_neg
  have he : Real.log (597164925831 / 500000000000) = -Real.log (500000000000 / 597164925831) := by
    rw [show ((597164925831 / 500000000000) : ℝ) = ((500000000000 / 597164925831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3664_neg : (11127803 / 62500000) ≤ -Real.log (250000000000 / 298719727133) ∧
    -Real.log (250000000000 / 298719727133) ≤ (178044849 / 1000000000) := by
  have h := checkLog_sound (w := (48719727133 / 548719727133)) (n := 12)
    (lo := (11127803 / 62500000)) (hi := (178044849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298719727133 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298719727133 / 250000000000) = 1/(250000000000 / 298719727133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3664 : Bounds (11127803 / 62500000) (178044849 / 1000000000) (Real.log (298719727133 / 250000000000)) := by
  have h := reflection_log_3664_neg
  have he : Real.log (298719727133 / 250000000000) = -Real.log (250000000000 / 298719727133) := by
    rw [show ((298719727133 / 250000000000) : ℝ) = ((250000000000 / 298719727133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3665_neg : (89080703 / 250000000) ≤ -Real.log (100000000000 / 142806847153) ∧
    -Real.log (100000000000 / 142806847153) ≤ (356322813 / 1000000000) := by
  have h := checkLog_sound (w := (42806847153 / 242806847153)) (n := 12)
    (lo := (89080703 / 250000000)) (hi := (356322813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142806847153 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142806847153 / 100000000000) = 1/(100000000000 / 142806847153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3665 : Bounds (89080703 / 250000000) (356322813 / 1000000000) (Real.log (142806847153 / 100000000000)) := by
  have h := reflection_log_3665_neg
  have he : Real.log (142806847153 / 100000000000) = -Real.log (100000000000 / 142806847153) := by
    rw [show ((142806847153 / 100000000000) : ℝ) = ((100000000000 / 142806847153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3666_neg : (356529231 / 1000000000) ≤ -Real.log (250000000000 / 357090820787) ∧
    -Real.log (250000000000 / 357090820787) ≤ (22283077 / 62500000) := by
  have h := checkLog_sound (w := (107090820787 / 607090820787)) (n := 12)
    (lo := (356529231 / 1000000000)) (hi := (22283077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357090820787 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357090820787 / 250000000000) = 1/(250000000000 / 357090820787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3666 : Bounds (356529231 / 1000000000) (22283077 / 62500000) (Real.log (357090820787 / 250000000000)) := by
  have h := reflection_log_3666_neg
  have he : Real.log (357090820787 / 250000000000) = -Real.log (250000000000 / 357090820787) := by
    rw [show ((357090820787 / 250000000000) : ℝ) = ((250000000000 / 357090820787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3667_neg : (162543929 / 1000000000) ≤ -Real.log (2000 / 2353) ∧
    -Real.log (2000 / 2353) ≤ (16254393 / 100000000) := by
  have h := checkLog_sound (w := (353 / 4353)) (n := 12)
    (lo := (162543929 / 1000000000)) (hi := (16254393 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 2000) = 1/(2000 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3667 : Bounds (162543929 / 1000000000) (16254393 / 100000000) (Real.log (2353 / 2000)) := by
  have h := reflection_log_3667_neg
  have he : Real.log (2353 / 2000) = -Real.log (2000 / 2353) := by
    rw [show ((2353 / 2000) : ℝ) = ((2000 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3668_neg : (194191729 / 1000000000) ≤ -Real.log (1647 / 2000) ∧
    -Real.log (1647 / 2000) ≤ (19419173 / 100000000) := by
  have h := checkLog_sound (w := (353 / 3647)) (n := 12)
    (lo := (194191729 / 1000000000)) (hi := (19419173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1647) = 1/(1647 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3668 : Bounds (-19419173 / 100000000) (-194191729 / 1000000000) (Real.log (1647 / 2000)) := by
  have h := reflection_log_3668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3669_neg : (44121 / 250000000) ≤ -Real.log (2000000 / 2000353) ∧
    -Real.log (2000000 / 2000353) ≤ (35297 / 200000000) := by
  have h := checkLog_sound (w := (353 / 4000353)) (n := 12)
    (lo := (44121 / 250000000)) (hi := (35297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000353 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000353 / 2000000) = 1/(2000000 / 2000353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3669 : Bounds (44121 / 250000000) (35297 / 200000000) (Real.log (2000353 / 2000000)) := by
  have h := reflection_log_3669_neg
  have he : Real.log (2000353 / 2000000) = -Real.log (2000000 / 2000353) := by
    rw [show ((2000353 / 2000000) : ℝ) = ((2000000 / 2000353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3670_neg : (35303 / 200000000) ≤ -Real.log (1999647 / 2000000) ∧
    -Real.log (1999647 / 2000000) ≤ (44129 / 250000000) := by
  have h := checkLog_sound (w := (353 / 3999647)) (n := 12)
    (lo := (35303 / 200000000)) (hi := (44129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999647) = 1/(1999647 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3670 : Bounds (-44129 / 250000000) (-35303 / 200000000) (Real.log (1999647 / 2000000)) := by
  have h := reflection_log_3670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3671_neg : (84902571 / 1000000000) ≤ -Real.log (1000000 / 1088611) ∧
    -Real.log (1000000 / 1088611) ≤ (21225643 / 250000000) := by
  have h := checkLog_sound (w := (88611 / 2088611)) (n := 12)
    (lo := (84902571 / 1000000000)) (hi := (21225643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088611 / 1000000) = 1/(1000000 / 1088611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3671 : Bounds (84902571 / 1000000000) (21225643 / 250000000) (Real.log (1088611 / 1000000)) := by
  have h := reflection_log_3671_neg
  have he : Real.log (1088611 / 1000000) = -Real.log (1000000 / 1088611) := by
    rw [show ((1088611 / 1000000) : ℝ) = ((1000000 / 1088611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3672_neg : (92785469 / 1000000000) ≤ -Real.log (911389 / 1000000) ∧
    -Real.log (911389 / 1000000) ≤ (9278547 / 100000000) := by
  have h := checkLog_sound (w := (88611 / 1911389)) (n := 12)
    (lo := (92785469 / 1000000000)) (hi := (9278547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911389) = 1/(911389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3672 : Bounds (-9278547 / 100000000) (-92785469 / 1000000000) (Real.log (911389 / 1000000)) := by
  have h := reflection_log_3672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3673_neg : (8511199 / 100000000) ≤ -Real.log (1000000 / 1088839) ∧
    -Real.log (1000000 / 1088839) ≤ (85111991 / 1000000000) := by
  have h := checkLog_sound (w := (88839 / 2088839)) (n := 12)
    (lo := (8511199 / 100000000)) (hi := (85111991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088839 / 1000000) = 1/(1000000 / 1088839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3673 : Bounds (8511199 / 100000000) (85111991 / 1000000000) (Real.log (1088839 / 1000000)) := by
  have h := reflection_log_3673_neg
  have he : Real.log (1088839 / 1000000) = -Real.log (1000000 / 1088839) := by
    rw [show ((1088839 / 1000000) : ℝ) = ((1000000 / 1088839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3674_neg : (23258917 / 250000000) ≤ -Real.log (911161 / 1000000) ∧
    -Real.log (911161 / 1000000) ≤ (93035669 / 1000000000) := by
  have h := checkLog_sound (w := (88839 / 1911161)) (n := 12)
    (lo := (23258917 / 250000000)) (hi := (93035669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911161) = 1/(911161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3674 : Bounds (-93035669 / 1000000000) (-23258917 / 250000000) (Real.log (911161 / 1000000)) := by
  have h := reflection_log_3674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3675_neg : (7923677 / 1000000000) ≤ -Real.log (992107632079 / 1000000000000) ∧
    -Real.log (992107632079 / 1000000000000) ≤ (3961839 / 500000000) := by
  have h := checkLog_sound (w := (7892367921 / 1992107632079)) (n := 12)
    (lo := (7923677 / 1000000000)) (hi := (3961839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992107632079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992107632079) = 1/(992107632079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3675 : Bounds (-3961839 / 500000000) (-7923677 / 1000000000) (Real.log (992107632079 / 1000000000000)) := by
  have h := reflection_log_3675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3676_neg : (7882897 / 1000000000) ≤ -Real.log (992148090679 / 1000000000000) ∧
    -Real.log (992148090679 / 1000000000000) ≤ (3941449 / 500000000) := by
  have h := checkLog_sound (w := (7851909321 / 1992148090679)) (n := 12)
    (lo := (7882897 / 1000000000)) (hi := (3941449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992148090679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992148090679) = 1/(992148090679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3676 : Bounds (-3941449 / 500000000) (-7882897 / 1000000000) (Real.log (992148090679 / 1000000000000)) := by
  have h := reflection_log_3676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3677_neg : (177688041 / 1000000000) ≤ -Real.log (500000000000 / 597226321581) ∧
    -Real.log (500000000000 / 597226321581) ≤ (88844021 / 500000000) := by
  have h := checkLog_sound (w := (97226321581 / 1097226321581)) (n := 12)
    (lo := (177688041 / 1000000000)) (hi := (88844021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597226321581 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597226321581 / 500000000000) = 1/(500000000000 / 597226321581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3677 : Bounds (177688041 / 1000000000) (88844021 / 500000000) (Real.log (597226321581 / 500000000000)) := by
  have h := reflection_log_3677_neg
  have he : Real.log (597226321581 / 500000000000) = -Real.log (500000000000 / 597226321581) := by
    rw [show ((597226321581 / 500000000000) : ℝ) = ((500000000000 / 597226321581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3678_neg : (178147659 / 1000000000) ≤ -Real.log (100000000000 / 119500176149) ∧
    -Real.log (100000000000 / 119500176149) ≤ (8907383 / 50000000) := by
  have h := checkLog_sound (w := (19500176149 / 219500176149)) (n := 12)
    (lo := (178147659 / 1000000000)) (hi := (8907383 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119500176149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119500176149 / 100000000000) = 1/(100000000000 / 119500176149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3678 : Bounds (178147659 / 1000000000) (8907383 / 50000000) (Real.log (119500176149 / 100000000000)) := by
  have h := reflection_log_3678_neg
  have he : Real.log (119500176149 / 100000000000) = -Real.log (100000000000 / 119500176149) := by
    rw [show ((119500176149 / 100000000000) : ℝ) = ((100000000000 / 119500176149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3679_neg : (356529231 / 1000000000) ≤ -Real.log (500000000000 / 714181641573) ∧
    -Real.log (500000000000 / 714181641573) ≤ (22283077 / 62500000) := by
  have h := checkLog_sound (w := (214181641573 / 1214181641573)) (n := 12)
    (lo := (356529231 / 1000000000)) (hi := (22283077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714181641573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714181641573 / 500000000000) = 1/(500000000000 / 714181641573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3679 : Bounds (356529231 / 1000000000) (22283077 / 62500000) (Real.log (714181641573 / 500000000000)) := by
  have h := reflection_log_3679_neg
  have he : Real.log (714181641573 / 500000000000) = -Real.log (500000000000 / 714181641573) := by
    rw [show ((714181641573 / 500000000000) : ℝ) = ((500000000000 / 714181641573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3680_neg : (178367829 / 500000000) ≤ -Real.log (250000000000 / 357164541591) ∧
    -Real.log (250000000000 / 357164541591) ≤ (356735659 / 1000000000) := by
  have h := checkLog_sound (w := (107164541591 / 607164541591)) (n := 12)
    (lo := (178367829 / 500000000)) (hi := (356735659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357164541591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357164541591 / 250000000000) = 1/(250000000000 / 357164541591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3680 : Bounds (178367829 / 500000000) (356735659 / 1000000000) (Real.log (357164541591 / 250000000000)) := by
  have h := reflection_log_3680_neg
  have he : Real.log (357164541591 / 250000000000) = -Real.log (250000000000 / 357164541591) := by
    rw [show ((357164541591 / 250000000000) : ℝ) = ((250000000000 / 357164541591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3681_neg : (162628923 / 1000000000) ≤ -Real.log (5000 / 5883) ∧
    -Real.log (5000 / 5883) ≤ (40657231 / 250000000) := by
  have h := checkLog_sound (w := (883 / 10883)) (n := 12)
    (lo := (162628923 / 1000000000)) (hi := (40657231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5883 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5883 / 5000) = 1/(5000 / 5883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3681 : Bounds (162628923 / 1000000000) (40657231 / 250000000) (Real.log (5883 / 5000)) := by
  have h := reflection_log_3681_neg
  have he : Real.log (5883 / 5000) = -Real.log (5000 / 5883) := by
    rw [show ((5883 / 5000) : ℝ) = ((5000 / 5883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3682_neg : (194313169 / 1000000000) ≤ -Real.log (4117 / 5000) ∧
    -Real.log (4117 / 5000) ≤ (19431317 / 100000000) := by
  have h := checkLog_sound (w := (883 / 9117)) (n := 12)
    (lo := (194313169 / 1000000000)) (hi := (19431317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4117) = 1/(4117 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3682 : Bounds (-19431317 / 100000000) (-194313169 / 1000000000) (Real.log (4117 / 5000)) := by
  have h := reflection_log_3682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3683_neg : (22073 / 125000000) ≤ -Real.log (5000000 / 5000883) ∧
    -Real.log (5000000 / 5000883) ≤ (35317 / 200000000) := by
  have h := checkLog_sound (w := (883 / 10000883)) (n := 12)
    (lo := (22073 / 125000000)) (hi := (35317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000883 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000883 / 5000000) = 1/(5000000 / 5000883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3683 : Bounds (22073 / 125000000) (35317 / 200000000) (Real.log (5000883 / 5000000)) := by
  have h := reflection_log_3683_neg
  have he : Real.log (5000883 / 5000000) = -Real.log (5000000 / 5000883) := by
    rw [show ((5000883 / 5000000) : ℝ) = ((5000000 / 5000883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3684_neg : (35323 / 200000000) ≤ -Real.log (4999117 / 5000000) ∧
    -Real.log (4999117 / 5000000) ≤ (22077 / 125000000) := by
  have h := checkLog_sound (w := (883 / 9999117)) (n := 12)
    (lo := (35323 / 200000000)) (hi := (22077 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999117) = 1/(4999117 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3684 : Bounds (-22077 / 125000000) (-35323 / 200000000) (Real.log (4999117 / 5000000)) := by
  have h := reflection_log_3684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3685_neg : (84949419 / 1000000000) ≤ -Real.log (500000 / 544331) ∧
    -Real.log (500000 / 544331) ≤ (4247471 / 50000000) := by
  have h := checkLog_sound (w := (44331 / 1044331)) (n := 12)
    (lo := (84949419 / 1000000000)) (hi := (4247471 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544331 / 500000) = 1/(500000 / 544331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3685 : Bounds (84949419 / 1000000000) (4247471 / 50000000) (Real.log (544331 / 500000)) := by
  have h := reflection_log_3685_neg
  have he : Real.log (544331 / 500000) = -Real.log (500000 / 544331) := by
    rw [show ((544331 / 500000) : ℝ) = ((500000 / 544331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3686_neg : (92841429 / 1000000000) ≤ -Real.log (455669 / 500000) ∧
    -Real.log (455669 / 500000) ≤ (9284143 / 100000000) := by
  have h := checkLog_sound (w := (44331 / 955669)) (n := 12)
    (lo := (92841429 / 1000000000)) (hi := (9284143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455669) = 1/(455669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3686 : Bounds (-9284143 / 100000000) (-92841429 / 1000000000) (Real.log (455669 / 500000)) := by
  have h := reflection_log_3686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3687_neg : (8515791 / 100000000) ≤ -Real.log (1000000 / 1088889) ∧
    -Real.log (1000000 / 1088889) ≤ (85157911 / 1000000000) := by
  have h := checkLog_sound (w := (88889 / 2088889)) (n := 12)
    (lo := (8515791 / 100000000)) (hi := (85157911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088889 / 1000000) = 1/(1000000 / 1088889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3687 : Bounds (8515791 / 100000000) (85157911 / 1000000000) (Real.log (1088889 / 1000000)) := by
  have h := reflection_log_3687_neg
  have he : Real.log (1088889 / 1000000) = -Real.log (1000000 / 1088889) := by
    rw [show ((1088889 / 1000000) : ℝ) = ((1000000 / 1088889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3688_neg : (18618109 / 200000000) ≤ -Real.log (911111 / 1000000) ∧
    -Real.log (911111 / 1000000) ≤ (46545273 / 500000000) := by
  have h := checkLog_sound (w := (88889 / 1911111)) (n := 12)
    (lo := (18618109 / 200000000)) (hi := (46545273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911111) = 1/(911111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3688 : Bounds (-46545273 / 500000000) (-18618109 / 200000000) (Real.log (911111 / 1000000)) := by
  have h := reflection_log_3688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3689_neg : (3966317 / 500000000) ≤ -Real.log (992098745679 / 1000000000000) ∧
    -Real.log (992098745679 / 1000000000000) ≤ (1586527 / 200000000) := by
  have h := checkLog_sound (w := (7901254321 / 1992098745679)) (n := 12)
    (lo := (3966317 / 500000000)) (hi := (1586527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992098745679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992098745679) = 1/(992098745679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3689 : Bounds (-1586527 / 200000000) (-3966317 / 500000000) (Real.log (992098745679 / 1000000000000)) := by
  have h := reflection_log_3689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3690_neg : (789201 / 100000000) ≤ -Real.log (248034762439 / 250000000000) ∧
    -Real.log (248034762439 / 250000000000) ≤ (7892011 / 1000000000) := by
  have h := checkLog_sound (w := (1965237561 / 498034762439)) (n := 12)
    (lo := (789201 / 100000000)) (hi := (7892011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248034762439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248034762439) = 1/(248034762439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3690 : Bounds (-7892011 / 1000000000) (-789201 / 100000000) (Real.log (248034762439 / 250000000000)) := by
  have h := reflection_log_3690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3691_neg : (1388991 / 7812500) ≤ -Real.log (500000000000 / 597287724203) ∧
    -Real.log (500000000000 / 597287724203) ≤ (177790849 / 1000000000) := by
  have h := checkLog_sound (w := (97287724203 / 1097287724203)) (n := 12)
    (lo := (1388991 / 7812500)) (hi := (177790849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597287724203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597287724203 / 500000000000) = 1/(500000000000 / 597287724203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3691 : Bounds (1388991 / 7812500) (177790849 / 1000000000) (Real.log (597287724203 / 500000000000)) := by
  have h := reflection_log_3691_neg
  have he : Real.log (597287724203 / 500000000000) = -Real.log (500000000000 / 597287724203) := by
    rw [show ((597287724203 / 500000000000) : ℝ) = ((500000000000 / 597287724203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3692_neg : (35649691 / 200000000) ≤ -Real.log (500000000000 / 597561109459) ∧
    -Real.log (500000000000 / 597561109459) ≤ (22281057 / 125000000) := by
  have h := checkLog_sound (w := (97561109459 / 1097561109459)) (n := 12)
    (lo := (35649691 / 200000000)) (hi := (22281057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597561109459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597561109459 / 500000000000) = 1/(500000000000 / 597561109459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3692 : Bounds (35649691 / 200000000) (22281057 / 125000000) (Real.log (597561109459 / 500000000000)) := by
  have h := reflection_log_3692_neg
  have he : Real.log (597561109459 / 500000000000) = -Real.log (500000000000 / 597561109459) := by
    rw [show ((597561109459 / 500000000000) : ℝ) = ((500000000000 / 597561109459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3693_neg : (178367829 / 500000000) ≤ -Real.log (500000000000 / 714329083181) ∧
    -Real.log (500000000000 / 714329083181) ≤ (356735659 / 1000000000) := by
  have h := checkLog_sound (w := (214329083181 / 1214329083181)) (n := 12)
    (lo := (178367829 / 500000000)) (hi := (356735659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714329083181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714329083181 / 500000000000) = 1/(500000000000 / 714329083181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3693 : Bounds (178367829 / 500000000) (356735659 / 1000000000) (Real.log (714329083181 / 500000000000)) := by
  have h := reflection_log_3693_neg
  have he : Real.log (714329083181 / 500000000000) = -Real.log (500000000000 / 714329083181) := by
    rw [show ((714329083181 / 500000000000) : ℝ) = ((500000000000 / 714329083181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3694_neg : (356942093 / 1000000000) ≤ -Real.log (500000000000 / 714476560603) ∧
    -Real.log (500000000000 / 714476560603) ≤ (178471047 / 500000000) := by
  have h := checkLog_sound (w := (214476560603 / 1214476560603)) (n := 12)
    (lo := (356942093 / 1000000000)) (hi := (178471047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714476560603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714476560603 / 500000000000) = 1/(500000000000 / 714476560603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3694 : Bounds (356942093 / 1000000000) (178471047 / 500000000) (Real.log (714476560603 / 500000000000)) := by
  have h := reflection_log_3694_neg
  have he : Real.log (714476560603 / 500000000000) = -Real.log (500000000000 / 714476560603) := by
    rw [show ((714476560603 / 500000000000) : ℝ) = ((500000000000 / 714476560603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3695_neg : (16271391 / 100000000) ≤ -Real.log (10000 / 11767) ∧
    -Real.log (10000 / 11767) ≤ (162713911 / 1000000000) := by
  have h := checkLog_sound (w := (1767 / 21767)) (n := 12)
    (lo := (16271391 / 100000000)) (hi := (162713911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11767 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11767 / 10000) = 1/(10000 / 11767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3695 : Bounds (16271391 / 100000000) (162713911 / 1000000000) (Real.log (11767 / 10000)) := by
  have h := reflection_log_3695_neg
  have he : Real.log (11767 / 10000) = -Real.log (10000 / 11767) := by
    rw [show ((11767 / 10000) : ℝ) = ((10000 / 11767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3696_neg : (3038041 / 15625000) ≤ -Real.log (8233 / 10000) ∧
    -Real.log (8233 / 10000) ≤ (1555477 / 8000000) := by
  have h := checkLog_sound (w := (1767 / 18233)) (n := 12)
    (lo := (3038041 / 15625000)) (hi := (1555477 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8233) = 1/(8233 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3696 : Bounds (-1555477 / 8000000) (-3038041 / 15625000) (Real.log (8233 / 10000)) := by
  have h := reflection_log_3696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3697_neg : (44171 / 250000000) ≤ -Real.log (10000000 / 10001767) ∧
    -Real.log (10000000 / 10001767) ≤ (35337 / 200000000) := by
  have h := checkLog_sound (w := (1767 / 20001767)) (n := 12)
    (lo := (44171 / 250000000)) (hi := (35337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001767 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001767 / 10000000) = 1/(10000000 / 10001767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3697 : Bounds (44171 / 250000000) (35337 / 200000000) (Real.log (10001767 / 10000000)) := by
  have h := reflection_log_3697_neg
  have he : Real.log (10001767 / 10000000) = -Real.log (10000000 / 10001767) := by
    rw [show ((10001767 / 10000000) : ℝ) = ((10000000 / 10001767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3698_neg : (35343 / 200000000) ≤ -Real.log (9998233 / 10000000) ∧
    -Real.log (9998233 / 10000000) ≤ (44179 / 250000000) := by
  have h := checkLog_sound (w := (1767 / 19998233)) (n := 12)
    (lo := (35343 / 200000000)) (hi := (44179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998233) = 1/(9998233 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3698 : Bounds (-44179 / 250000000) (-35343 / 200000000) (Real.log (9998233 / 10000000)) := by
  have h := reflection_log_3698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3699_neg : (10624533 / 125000000) ≤ -Real.log (1000000 / 1088713) ∧
    -Real.log (1000000 / 1088713) ≤ (16999253 / 200000000) := by
  have h := checkLog_sound (w := (88713 / 2088713)) (n := 12)
    (lo := (10624533 / 125000000)) (hi := (16999253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088713 / 1000000) = 1/(1000000 / 1088713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3699 : Bounds (10624533 / 125000000) (16999253 / 200000000) (Real.log (1088713 / 1000000)) := by
  have h := reflection_log_3699_neg
  have he : Real.log (1088713 / 1000000) = -Real.log (1000000 / 1088713) := by
    rw [show ((1088713 / 1000000) : ℝ) = ((1000000 / 1088713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3700_neg : (5806087 / 62500000) ≤ -Real.log (911287 / 1000000) ∧
    -Real.log (911287 / 1000000) ≤ (92897393 / 1000000000) := by
  have h := checkLog_sound (w := (88713 / 1911287)) (n := 12)
    (lo := (5806087 / 62500000)) (hi := (92897393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911287) = 1/(911287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3700 : Bounds (-92897393 / 1000000000) (-5806087 / 62500000) (Real.log (911287 / 1000000)) := by
  have h := reflection_log_3700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3701_neg : (42602373 / 500000000) ≤ -Real.log (50000 / 54447) ∧
    -Real.log (50000 / 54447) ≤ (85204747 / 1000000000) := by
  have h := checkLog_sound (w := (4447 / 104447)) (n := 12)
    (lo := (42602373 / 500000000)) (hi := (85204747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54447 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54447 / 50000) = 1/(50000 / 54447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3701 : Bounds (42602373 / 500000000) (85204747 / 1000000000) (Real.log (54447 / 50000)) := by
  have h := reflection_log_3701_neg
  have he : Real.log (54447 / 50000) = -Real.log (50000 / 54447) := by
    rw [show ((54447 / 50000) : ℝ) = ((50000 / 54447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3702_neg : (46573261 / 500000000) ≤ -Real.log (45553 / 50000) ∧
    -Real.log (45553 / 50000) ≤ (93146523 / 1000000000) := by
  have h := checkLog_sound (w := (4447 / 95553)) (n := 12)
    (lo := (46573261 / 500000000)) (hi := (93146523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45553) = 1/(45553 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3702 : Bounds (-93146523 / 1000000000) (-46573261 / 500000000) (Real.log (45553 / 50000)) := by
  have h := reflection_log_3702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3703_neg : (496361 / 62500000) ≤ -Real.log (2480224191 / 2500000000) ∧
    -Real.log (2480224191 / 2500000000) ≤ (7941777 / 1000000000) := by
  have h := checkLog_sound (w := (19775809 / 4980224191)) (n := 12)
    (lo := (496361 / 62500000)) (hi := (7941777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2480224191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2480224191) = 1/(2480224191 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3703 : Bounds (-7941777 / 1000000000) (-496361 / 62500000) (Real.log (2480224191 / 2500000000)) := by
  have h := reflection_log_3703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3704_neg : (987641 / 125000000) ≤ -Real.log (992130003631 / 1000000000000) ∧
    -Real.log (992130003631 / 1000000000000) ≤ (7901129 / 1000000000) := by
  have h := checkLog_sound (w := (7869996369 / 1992130003631)) (n := 12)
    (lo := (987641 / 125000000)) (hi := (7901129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992130003631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992130003631) = 1/(992130003631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3704 : Bounds (-7901129 / 1000000000) (-987641 / 125000000) (Real.log (992130003631 / 1000000000000)) := by
  have h := reflection_log_3704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3705_neg : (177893657 / 1000000000) ≤ -Real.log (500000000000 / 597349133697) ∧
    -Real.log (500000000000 / 597349133697) ≤ (88946829 / 500000000) := by
  have h := checkLog_sound (w := (97349133697 / 1097349133697)) (n := 12)
    (lo := (177893657 / 1000000000)) (hi := (88946829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597349133697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597349133697 / 500000000000) = 1/(500000000000 / 597349133697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3705 : Bounds (177893657 / 1000000000) (88946829 / 500000000) (Real.log (597349133697 / 500000000000)) := by
  have h := reflection_log_3705_neg
  have he : Real.log (597349133697 / 500000000000) = -Real.log (500000000000 / 597349133697) := by
    rw [show ((597349133697 / 500000000000) : ℝ) = ((500000000000 / 597349133697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3706_neg : (44587817 / 250000000) ≤ -Real.log (250000000000 / 298811274779) ∧
    -Real.log (250000000000 / 298811274779) ≤ (178351269 / 1000000000) := by
  have h := checkLog_sound (w := (48811274779 / 548811274779)) (n := 12)
    (lo := (44587817 / 250000000)) (hi := (178351269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298811274779 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298811274779 / 250000000000) = 1/(250000000000 / 298811274779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3706 : Bounds (44587817 / 250000000) (178351269 / 1000000000) (Real.log (298811274779 / 250000000000)) := by
  have h := reflection_log_3706_neg
  have he : Real.log (298811274779 / 250000000000) = -Real.log (250000000000 / 298811274779) := by
    rw [show ((298811274779 / 250000000000) : ℝ) = ((250000000000 / 298811274779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3707_neg : (356942093 / 1000000000) ≤ -Real.log (250000000000 / 357238280301) ∧
    -Real.log (250000000000 / 357238280301) ≤ (178471047 / 500000000) := by
  have h := checkLog_sound (w := (107238280301 / 607238280301)) (n := 12)
    (lo := (356942093 / 1000000000)) (hi := (178471047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357238280301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357238280301 / 250000000000) = 1/(250000000000 / 357238280301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3707 : Bounds (356942093 / 1000000000) (178471047 / 500000000) (Real.log (357238280301 / 250000000000)) := by
  have h := reflection_log_3707_neg
  have he : Real.log (357238280301 / 250000000000) = -Real.log (250000000000 / 357238280301) := by
    rw [show ((357238280301 / 250000000000) : ℝ) = ((250000000000 / 357238280301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3708_neg : (71429707 / 200000000) ≤ -Real.log (10000000000 / 14292481477) ∧
    -Real.log (10000000000 / 14292481477) ≤ (44643567 / 125000000) := by
  have h := checkLog_sound (w := (4292481477 / 24292481477)) (n := 12)
    (lo := (71429707 / 200000000)) (hi := (44643567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14292481477 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14292481477 / 10000000000) = 1/(10000000000 / 14292481477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3708 : Bounds (71429707 / 200000000) (44643567 / 125000000) (Real.log (14292481477 / 10000000000)) := by
  have h := reflection_log_3708_neg
  have he : Real.log (14292481477 / 10000000000) = -Real.log (10000000000 / 14292481477) := by
    rw [show ((14292481477 / 10000000000) : ℝ) = ((10000000000 / 14292481477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3709_neg : (16279889 / 100000000) ≤ -Real.log (1250 / 1471) ∧
    -Real.log (1250 / 1471) ≤ (162798891 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2721)) (n := 12)
    (lo := (16279889 / 100000000)) (hi := (162798891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471 / 1250) = 1/(1250 / 1471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3709 : Bounds (16279889 / 100000000) (162798891 / 1000000000) (Real.log (1471 / 1250)) := by
  have h := reflection_log_3709_neg
  have he : Real.log (1471 / 1250) = -Real.log (1250 / 1471) := by
    rw [show ((1471 / 1250) : ℝ) = ((1250 / 1471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3710_neg : (97278047 / 500000000) ≤ -Real.log (1029 / 1250) ∧
    -Real.log (1029 / 1250) ≤ (38911219 / 200000000) := by
  have h := checkLog_sound (w := (221 / 2279)) (n := 12)
    (lo := (97278047 / 500000000)) (hi := (38911219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1029) = 1/(1029 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3710 : Bounds (-38911219 / 200000000) (-97278047 / 500000000) (Real.log (1029 / 1250)) := by
  have h := reflection_log_3710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3711_neg : (11049 / 62500000) ≤ -Real.log (1250000 / 1250221) ∧
    -Real.log (1250000 / 1250221) ≤ (35357 / 200000000) := by
  have h := checkLog_sound (w := (221 / 2500221)) (n := 12)
    (lo := (11049 / 62500000)) (hi := (35357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250221 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250221 / 1250000) = 1/(1250000 / 1250221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3711 : Bounds (11049 / 62500000) (35357 / 200000000) (Real.log (1250221 / 1250000)) := by
  have h := reflection_log_3711_neg
  have he : Real.log (1250221 / 1250000) = -Real.log (1250000 / 1250221) := by
    rw [show ((1250221 / 1250000) : ℝ) = ((1250000 / 1250221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0058 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3712_neg : (35363 / 200000000) ≤ -Real.log (1249779 / 1250000) ∧
    -Real.log (1249779 / 1250000) ≤ (11051 / 62500000) := by
  have h := checkLog_sound (w := (221 / 2499779)) (n := 12)
    (lo := (35363 / 200000000)) (hi := (11051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249779) = 1/(1249779 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3712 : Bounds (-11051 / 62500000) (-35363 / 200000000) (Real.log (1249779 / 1250000)) := by
  have h := reflection_log_3712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3713_neg : (85043107 / 1000000000) ≤ -Real.log (250000 / 272191) ∧
    -Real.log (250000 / 272191) ≤ (21260777 / 250000000) := by
  have h := checkLog_sound (w := (22191 / 522191)) (n := 12)
    (lo := (85043107 / 1000000000)) (hi := (21260777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272191 / 250000) = 1/(250000 / 272191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3713 : Bounds (85043107 / 1000000000) (21260777 / 250000000) (Real.log (272191 / 250000)) := by
  have h := reflection_log_3713_neg
  have he : Real.log (272191 / 250000) = -Real.log (250000 / 272191) := by
    rw [show ((272191 / 250000) : ℝ) = ((250000 / 272191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3714_neg : (92953359 / 1000000000) ≤ -Real.log (227809 / 250000) ∧
    -Real.log (227809 / 250000) ≤ (1161917 / 12500000) := by
  have h := checkLog_sound (w := (22191 / 477809)) (n := 12)
    (lo := (92953359 / 1000000000)) (hi := (1161917 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227809) = 1/(227809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3714 : Bounds (-1161917 / 12500000) (-92953359 / 1000000000) (Real.log (227809 / 250000)) := by
  have h := reflection_log_3714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3715_neg : (85251579 / 1000000000) ≤ -Real.log (1000000 / 1088991) ∧
    -Real.log (1000000 / 1088991) ≤ (4262579 / 50000000) := by
  have h := checkLog_sound (w := (88991 / 2088991)) (n := 12)
    (lo := (85251579 / 1000000000)) (hi := (4262579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088991 / 1000000) = 1/(1000000 / 1088991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3715 : Bounds (85251579 / 1000000000) (4262579 / 50000000) (Real.log (1088991 / 1000000)) := by
  have h := reflection_log_3715_neg
  have he : Real.log (1088991 / 1000000) = -Real.log (1000000 / 1088991) := by
    rw [show ((1088991 / 1000000) : ℝ) = ((1000000 / 1088991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3716_neg : (46601251 / 500000000) ≤ -Real.log (911009 / 1000000) ∧
    -Real.log (911009 / 1000000) ≤ (93202503 / 1000000000) := by
  have h := checkLog_sound (w := (88991 / 1911009)) (n := 12)
    (lo := (46601251 / 500000000)) (hi := (93202503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911009) = 1/(911009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3716 : Bounds (-93202503 / 1000000000) (-46601251 / 500000000) (Real.log (911009 / 1000000)) := by
  have h := reflection_log_3716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3717_neg : (7950923 / 1000000000) ≤ -Real.log (992080601919 / 1000000000000) ∧
    -Real.log (992080601919 / 1000000000000) ≤ (1987731 / 250000000) := by
  have h := checkLog_sound (w := (7919398081 / 1992080601919)) (n := 12)
    (lo := (7950923 / 1000000000)) (hi := (1987731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992080601919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992080601919) = 1/(992080601919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3717 : Bounds (-1987731 / 250000000) (-7950923 / 1000000000) (Real.log (992080601919 / 1000000000000)) := by
  have h := reflection_log_3717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3718_neg : (7910251 / 1000000000) ≤ -Real.log (62007559519 / 62500000000) ∧
    -Real.log (62007559519 / 62500000000) ≤ (1977563 / 250000000) := by
  have h := checkLog_sound (w := (492440481 / 124507559519)) (n := 12)
    (lo := (7910251 / 1000000000)) (hi := (1977563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62007559519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62007559519) = 1/(62007559519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3718 : Bounds (-1977563 / 250000000) (-7910251 / 1000000000) (Real.log (62007559519 / 62500000000)) := by
  have h := reflection_log_3718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3719_neg : (177996467 / 1000000000) ≤ -Real.log (250000000000 / 298705275033) ∧
    -Real.log (250000000000 / 298705275033) ≤ (44499117 / 250000000) := by
  have h := checkLog_sound (w := (48705275033 / 548705275033)) (n := 12)
    (lo := (177996467 / 1000000000)) (hi := (44499117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298705275033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298705275033 / 250000000000) = 1/(250000000000 / 298705275033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3719 : Bounds (177996467 / 1000000000) (44499117 / 250000000) (Real.log (298705275033 / 250000000000)) := by
  have h := reflection_log_3719_neg
  have he : Real.log (298705275033 / 250000000000) = -Real.log (250000000000 / 298705275033) := by
    rw [show ((298705275033 / 250000000000) : ℝ) = ((250000000000 / 298705275033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3720_neg : (178454081 / 1000000000) ≤ -Real.log (62500000000 / 74710499567) ∧
    -Real.log (62500000000 / 74710499567) ≤ (89227041 / 500000000) := by
  have h := checkLog_sound (w := (12210499567 / 137210499567)) (n := 12)
    (lo := (178454081 / 1000000000)) (hi := (89227041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74710499567 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74710499567 / 62500000000) = 1/(62500000000 / 74710499567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3720 : Bounds (178454081 / 1000000000) (89227041 / 500000000) (Real.log (74710499567 / 62500000000)) := by
  have h := reflection_log_3720_neg
  have he : Real.log (74710499567 / 62500000000) = -Real.log (62500000000 / 74710499567) := by
    rw [show ((74710499567 / 62500000000) : ℝ) = ((62500000000 / 74710499567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3721_neg : (71429707 / 200000000) ≤ -Real.log (500000000000 / 714624073849) ∧
    -Real.log (500000000000 / 714624073849) ≤ (44643567 / 125000000) := by
  have h := checkLog_sound (w := (214624073849 / 1214624073849)) (n := 12)
    (lo := (71429707 / 200000000)) (hi := (44643567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714624073849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714624073849 / 500000000000) = 1/(500000000000 / 714624073849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3721 : Bounds (71429707 / 200000000) (44643567 / 125000000) (Real.log (714624073849 / 500000000000)) := by
  have h := reflection_log_3721_neg
  have he : Real.log (714624073849 / 500000000000) = -Real.log (500000000000 / 714624073849) := by
    rw [show ((714624073849 / 500000000000) : ℝ) = ((500000000000 / 714624073849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3722_neg : (44669373 / 125000000) ≤ -Real.log (100000000000 / 142954324587) ∧
    -Real.log (100000000000 / 142954324587) ≤ (71470997 / 200000000) := by
  have h := checkLog_sound (w := (42954324587 / 242954324587)) (n := 12)
    (lo := (44669373 / 125000000)) (hi := (71470997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142954324587 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142954324587 / 100000000000) = 1/(100000000000 / 142954324587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3722 : Bounds (44669373 / 125000000) (71470997 / 200000000) (Real.log (142954324587 / 100000000000)) := by
  have h := reflection_log_3722_neg
  have he : Real.log (142954324587 / 100000000000) = -Real.log (100000000000 / 142954324587) := by
    rw [show ((142954324587 / 100000000000) : ℝ) = ((100000000000 / 142954324587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3723_neg : (81441931 / 500000000) ≤ -Real.log (10000 / 11769) ∧
    -Real.log (10000 / 11769) ≤ (162883863 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 21769)) (n := 12)
    (lo := (81441931 / 500000000)) (hi := (162883863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11769 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11769 / 10000) = 1/(10000 / 11769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3723 : Bounds (81441931 / 500000000) (162883863 / 1000000000) (Real.log (11769 / 10000)) := by
  have h := reflection_log_3723_neg
  have he : Real.log (11769 / 10000) = -Real.log (10000 / 11769) := by
    rw [show ((11769 / 10000) : ℝ) = ((10000 / 11769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3724_neg : (194677579 / 1000000000) ≤ -Real.log (8231 / 10000) ∧
    -Real.log (8231 / 10000) ≤ (9733879 / 50000000) := by
  have h := checkLog_sound (w := (1769 / 18231)) (n := 12)
    (lo := (194677579 / 1000000000)) (hi := (9733879 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8231) = 1/(8231 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3724 : Bounds (-9733879 / 50000000) (-194677579 / 1000000000) (Real.log (8231 / 10000)) := by
  have h := reflection_log_3724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3725_neg : (44221 / 250000000) ≤ -Real.log (10000000 / 10001769) ∧
    -Real.log (10000000 / 10001769) ≤ (35377 / 200000000) := by
  have h := checkLog_sound (w := (1769 / 20001769)) (n := 12)
    (lo := (44221 / 250000000)) (hi := (35377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001769 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001769 / 10000000) = 1/(10000000 / 10001769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3725 : Bounds (44221 / 250000000) (35377 / 200000000) (Real.log (10001769 / 10000000)) := by
  have h := reflection_log_3725_neg
  have he : Real.log (10001769 / 10000000) = -Real.log (10000000 / 10001769) := by
    rw [show ((10001769 / 10000000) : ℝ) = ((10000000 / 10001769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3726_neg : (35383 / 200000000) ≤ -Real.log (9998231 / 10000000) ∧
    -Real.log (9998231 / 10000000) ≤ (44229 / 250000000) := by
  have h := checkLog_sound (w := (1769 / 19998231)) (n := 12)
    (lo := (35383 / 200000000)) (hi := (44229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998231) = 1/(9998231 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3726 : Bounds (-44229 / 250000000) (-35383 / 200000000) (Real.log (9998231 / 10000000)) := by
  have h := reflection_log_3726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3727_neg : (21272487 / 250000000) ≤ -Real.log (200000 / 217763) ∧
    -Real.log (200000 / 217763) ≤ (85089949 / 1000000000) := by
  have h := checkLog_sound (w := (17763 / 417763)) (n := 12)
    (lo := (21272487 / 250000000)) (hi := (85089949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217763 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217763 / 200000) = 1/(200000 / 217763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3727 : Bounds (21272487 / 250000000) (85089949 / 1000000000) (Real.log (217763 / 200000)) := by
  have h := reflection_log_3727_neg
  have he : Real.log (217763 / 200000) = -Real.log (200000 / 217763) := by
    rw [show ((217763 / 200000) : ℝ) = ((200000 / 217763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3728_neg : (5813083 / 62500000) ≤ -Real.log (182237 / 200000) ∧
    -Real.log (182237 / 200000) ≤ (93009329 / 1000000000) := by
  have h := checkLog_sound (w := (17763 / 382237)) (n := 12)
    (lo := (5813083 / 62500000)) (hi := (93009329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182237) = 1/(182237 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3728 : Bounds (-93009329 / 1000000000) (-5813083 / 62500000) (Real.log (182237 / 200000)) := by
  have h := reflection_log_3728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3729_neg : (8529841 / 100000000) ≤ -Real.log (500000 / 544521) ∧
    -Real.log (500000 / 544521) ≤ (85298411 / 1000000000) := by
  have h := checkLog_sound (w := (44521 / 1044521)) (n := 12)
    (lo := (8529841 / 100000000)) (hi := (85298411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544521 / 500000) = 1/(500000 / 544521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3729 : Bounds (8529841 / 100000000) (85298411 / 1000000000) (Real.log (544521 / 500000)) := by
  have h := reflection_log_3729_neg
  have he : Real.log (544521 / 500000) = -Real.log (500000 / 544521) := by
    rw [show ((544521 / 500000) : ℝ) = ((500000 / 544521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3730_neg : (18651697 / 200000000) ≤ -Real.log (455479 / 500000) ∧
    -Real.log (455479 / 500000) ≤ (46629243 / 500000000) := by
  have h := checkLog_sound (w := (44521 / 955479)) (n := 12)
    (lo := (18651697 / 200000000)) (hi := (46629243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455479) = 1/(455479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3730 : Bounds (-46629243 / 500000000) (-18651697 / 200000000) (Real.log (455479 / 500000)) := by
  have h := reflection_log_3730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3731_neg : (318403 / 40000000) ≤ -Real.log (248017880559 / 250000000000) ∧
    -Real.log (248017880559 / 250000000000) ≤ (1990019 / 250000000) := by
  have h := checkLog_sound (w := (1982119441 / 498017880559)) (n := 12)
    (lo := (318403 / 40000000)) (hi := (1990019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248017880559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248017880559) = 1/(248017880559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3731 : Bounds (-1990019 / 250000000) (-318403 / 40000000) (Real.log (248017880559 / 250000000000)) := by
  have h := reflection_log_3731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3732_neg : (7919379 / 1000000000) ≤ -Real.log (39684475831 / 40000000000) ∧
    -Real.log (39684475831 / 40000000000) ≤ (395969 / 50000000) := by
  have h := checkLog_sound (w := (315524169 / 79684475831)) (n := 12)
    (lo := (7919379 / 1000000000)) (hi := (395969 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39684475831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39684475831) = 1/(39684475831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3732 : Bounds (-395969 / 50000000) (-7919379 / 1000000000) (Real.log (39684475831 / 40000000000)) := by
  have h := reflection_log_3732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3733_neg : (178099277 / 1000000000) ≤ -Real.log (500000000000 / 597471973309) ∧
    -Real.log (500000000000 / 597471973309) ≤ (89049639 / 500000000) := by
  have h := checkLog_sound (w := (97471973309 / 1097471973309)) (n := 12)
    (lo := (178099277 / 1000000000)) (hi := (89049639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597471973309 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597471973309 / 500000000000) = 1/(500000000000 / 597471973309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3733 : Bounds (178099277 / 1000000000) (89049639 / 500000000) (Real.log (597471973309 / 500000000000)) := by
  have h := reflection_log_3733_neg
  have he : Real.log (597471973309 / 500000000000) = -Real.log (500000000000 / 597471973309) := by
    rw [show ((597471973309 / 500000000000) : ℝ) = ((500000000000 / 597471973309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3734_neg : (5579903 / 31250000) ≤ -Real.log (250000000000 / 298872725197) ∧
    -Real.log (250000000000 / 298872725197) ≤ (178556897 / 1000000000) := by
  have h := checkLog_sound (w := (48872725197 / 548872725197)) (n := 12)
    (lo := (5579903 / 31250000)) (hi := (178556897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298872725197 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298872725197 / 250000000000) = 1/(250000000000 / 298872725197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3734 : Bounds (5579903 / 31250000) (178556897 / 1000000000) (Real.log (298872725197 / 250000000000)) := by
  have h := reflection_log_3734_neg
  have he : Real.log (298872725197 / 250000000000) = -Real.log (250000000000 / 298872725197) := by
    rw [show ((298872725197 / 250000000000) : ℝ) = ((250000000000 / 298872725197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3735_neg : (44669373 / 125000000) ≤ -Real.log (250000000000 / 357385811467) ∧
    -Real.log (250000000000 / 357385811467) ≤ (71470997 / 200000000) := by
  have h := checkLog_sound (w := (107385811467 / 607385811467)) (n := 12)
    (lo := (44669373 / 125000000)) (hi := (71470997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357385811467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357385811467 / 250000000000) = 1/(250000000000 / 357385811467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3735 : Bounds (44669373 / 125000000) (71470997 / 200000000) (Real.log (357385811467 / 250000000000)) := by
  have h := reflection_log_3735_neg
  have he : Real.log (357385811467 / 250000000000) = -Real.log (250000000000 / 357385811467) := by
    rw [show ((357385811467 / 250000000000) : ℝ) = ((250000000000 / 357385811467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3736_neg : (357561441 / 1000000000) ≤ -Real.log (500000000000 / 714919207873) ∧
    -Real.log (500000000000 / 714919207873) ≤ (178780721 / 500000000) := by
  have h := checkLog_sound (w := (214919207873 / 1214919207873)) (n := 12)
    (lo := (357561441 / 1000000000)) (hi := (178780721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714919207873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714919207873 / 500000000000) = 1/(500000000000 / 714919207873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3736 : Bounds (357561441 / 1000000000) (178780721 / 500000000) (Real.log (714919207873 / 500000000000)) := by
  have h := reflection_log_3736_neg
  have he : Real.log (714919207873 / 500000000000) = -Real.log (500000000000 / 714919207873) := by
    rw [show ((714919207873 / 500000000000) : ℝ) = ((500000000000 / 714919207873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3737_neg : (40742207 / 250000000) ≤ -Real.log (1000 / 1177) ∧
    -Real.log (1000 / 1177) ≤ (162968829 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 2177)) (n := 12)
    (lo := (40742207 / 250000000)) (hi := (162968829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177 / 1000) = 1/(1000 / 1177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3737 : Bounds (40742207 / 250000000) (162968829 / 1000000000) (Real.log (1177 / 1000)) := by
  have h := reflection_log_3737_neg
  have he : Real.log (1177 / 1000) = -Real.log (1000 / 1177) := by
    rw [show ((1177 / 1000) : ℝ) = ((1000 / 1177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3738_neg : (97399539 / 500000000) ≤ -Real.log (823 / 1000) ∧
    -Real.log (823 / 1000) ≤ (194799079 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 1823)) (n := 12)
    (lo := (97399539 / 500000000)) (hi := (194799079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 823) = 1/(823 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3738 : Bounds (-194799079 / 1000000000) (-97399539 / 500000000) (Real.log (823 / 1000)) := by
  have h := reflection_log_3738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3739_neg : (22123 / 125000000) ≤ -Real.log (1000000 / 1000177) ∧
    -Real.log (1000000 / 1000177) ≤ (35397 / 200000000) := by
  have h := checkLog_sound (w := (177 / 2000177)) (n := 12)
    (lo := (22123 / 125000000)) (hi := (35397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000177 / 1000000) = 1/(1000000 / 1000177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3739 : Bounds (22123 / 125000000) (35397 / 200000000) (Real.log (1000177 / 1000000)) := by
  have h := reflection_log_3739_neg
  have he : Real.log (1000177 / 1000000) = -Real.log (1000000 / 1000177) := by
    rw [show ((1000177 / 1000000) : ℝ) = ((1000000 / 1000177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3740_neg : (35403 / 200000000) ≤ -Real.log (999823 / 1000000) ∧
    -Real.log (999823 / 1000000) ≤ (22127 / 125000000) := by
  have h := checkLog_sound (w := (177 / 1999823)) (n := 12)
    (lo := (35403 / 200000000)) (hi := (22127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999823) = 1/(999823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3740 : Bounds (-22127 / 125000000) (-35403 / 200000000) (Real.log (999823 / 1000000)) := by
  have h := reflection_log_3740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3741_neg : (85135869 / 1000000000) ≤ -Real.log (200000 / 217773) ∧
    -Real.log (200000 / 217773) ≤ (8513587 / 100000000) := by
  have h := checkLog_sound (w := (17773 / 417773)) (n := 12)
    (lo := (85135869 / 1000000000)) (hi := (8513587 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217773 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217773 / 200000) = 1/(200000 / 217773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3741 : Bounds (85135869 / 1000000000) (8513587 / 100000000) (Real.log (217773 / 200000)) := by
  have h := reflection_log_3741_neg
  have he : Real.log (217773 / 200000) = -Real.log (200000 / 217773) := by
    rw [show ((217773 / 200000) : ℝ) = ((200000 / 217773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3742_neg : (93064203 / 1000000000) ≤ -Real.log (182227 / 200000) ∧
    -Real.log (182227 / 200000) ≤ (23266051 / 250000000) := by
  have h := checkLog_sound (w := (17773 / 382227)) (n := 12)
    (lo := (93064203 / 1000000000)) (hi := (23266051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182227) = 1/(182227 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3742 : Bounds (-23266051 / 250000000) (-93064203 / 1000000000) (Real.log (182227 / 200000)) := by
  have h := reflection_log_3742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3743_neg : (85345239 / 1000000000) ≤ -Real.log (1000000 / 1089093) ∧
    -Real.log (1000000 / 1089093) ≤ (2133631 / 25000000) := by
  have h := checkLog_sound (w := (89093 / 2089093)) (n := 12)
    (lo := (85345239 / 1000000000)) (hi := (2133631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089093 / 1000000) = 1/(1000000 / 1089093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3743 : Bounds (85345239 / 1000000000) (2133631 / 25000000) (Real.log (1089093 / 1000000)) := by
  have h := reflection_log_3743_neg
  have he : Real.log (1089093 / 1000000) = -Real.log (1000000 / 1089093) := by
    rw [show ((1089093 / 1000000) : ℝ) = ((1000000 / 1089093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3744_neg : (11664309 / 125000000) ≤ -Real.log (910907 / 1000000) ∧
    -Real.log (910907 / 1000000) ≤ (93314473 / 1000000000) := by
  have h := checkLog_sound (w := (89093 / 1910907)) (n := 12)
    (lo := (11664309 / 125000000)) (hi := (93314473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910907) = 1/(910907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3744 : Bounds (-93314473 / 1000000000) (-11664309 / 125000000) (Real.log (910907 / 1000000)) := by
  have h := reflection_log_3744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3745_neg : (498077 / 62500000) ≤ -Real.log (992062437351 / 1000000000000) ∧
    -Real.log (992062437351 / 1000000000000) ≤ (7969233 / 1000000000) := by
  have h := checkLog_sound (w := (7937562649 / 1992062437351)) (n := 12)
    (lo := (498077 / 62500000)) (hi := (7969233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992062437351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992062437351) = 1/(992062437351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3745 : Bounds (-7969233 / 1000000000) (-498077 / 62500000) (Real.log (992062437351 / 1000000000000)) := by
  have h := reflection_log_3745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3746_neg : (3964167 / 500000000) ≤ -Real.log (39684120471 / 40000000000) ∧
    -Real.log (39684120471 / 40000000000) ≤ (1585667 / 200000000) := by
  have h := checkLog_sound (w := (315879529 / 79684120471)) (n := 12)
    (lo := (3964167 / 500000000)) (hi := (1585667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39684120471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39684120471) = 1/(39684120471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3746 : Bounds (-1585667 / 200000000) (-3964167 / 500000000) (Real.log (39684120471 / 40000000000)) := by
  have h := reflection_log_3746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3747_neg : (178200073 / 1000000000) ≤ -Real.log (10000000000 / 11950643977) ∧
    -Real.log (10000000000 / 11950643977) ≤ (89100037 / 500000000) := by
  have h := checkLog_sound (w := (1950643977 / 21950643977)) (n := 12)
    (lo := (178200073 / 1000000000)) (hi := (89100037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11950643977 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11950643977 / 10000000000) = 1/(10000000000 / 11950643977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3747 : Bounds (178200073 / 1000000000) (89100037 / 500000000) (Real.log (11950643977 / 10000000000)) := by
  have h := reflection_log_3747_neg
  have he : Real.log (11950643977 / 10000000000) = -Real.log (10000000000 / 11950643977) := by
    rw [show ((11950643977 / 10000000000) : ℝ) = ((10000000000 / 11950643977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3748_neg : (1395779 / 7812500) ≤ -Real.log (250000000000 / 298903455567) ∧
    -Real.log (250000000000 / 298903455567) ≤ (178659713 / 1000000000) := by
  have h := checkLog_sound (w := (48903455567 / 548903455567)) (n := 12)
    (lo := (1395779 / 7812500)) (hi := (178659713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298903455567 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298903455567 / 250000000000) = 1/(250000000000 / 298903455567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3748 : Bounds (1395779 / 7812500) (178659713 / 1000000000) (Real.log (298903455567 / 250000000000)) := by
  have h := reflection_log_3748_neg
  have he : Real.log (298903455567 / 250000000000) = -Real.log (250000000000 / 298903455567) := by
    rw [show ((298903455567 / 250000000000) : ℝ) = ((250000000000 / 298903455567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3749_neg : (357561441 / 1000000000) ≤ -Real.log (7812500000 / 11170612623) ∧
    -Real.log (7812500000 / 11170612623) ≤ (178780721 / 500000000) := by
  have h := checkLog_sound (w := (3358112623 / 18983112623)) (n := 12)
    (lo := (357561441 / 1000000000)) (hi := (178780721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11170612623 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11170612623 / 7812500000) = 1/(7812500000 / 11170612623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3749 : Bounds (357561441 / 1000000000) (178780721 / 500000000) (Real.log (11170612623 / 7812500000)) := by
  have h := reflection_log_3749_neg
  have he : Real.log (11170612623 / 7812500000) = -Real.log (7812500000 / 11170612623) := by
    rw [show ((11170612623 / 7812500000) : ℝ) = ((7812500000 / 11170612623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3750_neg : (178883953 / 500000000) ≤ -Real.log (125000000000 / 178766707169) ∧
    -Real.log (125000000000 / 178766707169) ≤ (357767907 / 1000000000) := by
  have h := checkLog_sound (w := (53766707169 / 303766707169)) (n := 12)
    (lo := (178883953 / 500000000)) (hi := (357767907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178766707169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178766707169 / 125000000000) = 1/(125000000000 / 178766707169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3750 : Bounds (178883953 / 500000000) (357767907 / 1000000000) (Real.log (178766707169 / 125000000000)) := by
  have h := reflection_log_3750_neg
  have he : Real.log (178766707169 / 125000000000) = -Real.log (125000000000 / 178766707169) := by
    rw [show ((178766707169 / 125000000000) : ℝ) = ((125000000000 / 178766707169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3751_neg : (81526893 / 500000000) ≤ -Real.log (10000 / 11771) ∧
    -Real.log (10000 / 11771) ≤ (163053787 / 1000000000) := by
  have h := checkLog_sound (w := (1771 / 21771)) (n := 12)
    (lo := (81526893 / 500000000)) (hi := (163053787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11771 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11771 / 10000) = 1/(10000 / 11771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3751 : Bounds (81526893 / 500000000) (163053787 / 1000000000) (Real.log (11771 / 10000)) := by
  have h := reflection_log_3751_neg
  have he : Real.log (11771 / 10000) = -Real.log (10000 / 11771) := by
    rw [show ((11771 / 10000) : ℝ) = ((10000 / 11771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3752_neg : (12182537 / 62500000) ≤ -Real.log (8229 / 10000) ∧
    -Real.log (8229 / 10000) ≤ (194920593 / 1000000000) := by
  have h := checkLog_sound (w := (1771 / 18229)) (n := 12)
    (lo := (12182537 / 62500000)) (hi := (194920593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8229) = 1/(8229 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3752 : Bounds (-194920593 / 1000000000) (-12182537 / 62500000) (Real.log (8229 / 10000)) := by
  have h := reflection_log_3752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3753_neg : (44271 / 250000000) ≤ -Real.log (10000000 / 10001771) ∧
    -Real.log (10000000 / 10001771) ≤ (35417 / 200000000) := by
  have h := checkLog_sound (w := (1771 / 20001771)) (n := 12)
    (lo := (44271 / 250000000)) (hi := (35417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001771 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001771 / 10000000) = 1/(10000000 / 10001771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3753 : Bounds (44271 / 250000000) (35417 / 200000000) (Real.log (10001771 / 10000000)) := by
  have h := reflection_log_3753_neg
  have he : Real.log (10001771 / 10000000) = -Real.log (10000000 / 10001771) := by
    rw [show ((10001771 / 10000000) : ℝ) = ((10000000 / 10001771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3754_neg : (35423 / 200000000) ≤ -Real.log (9998229 / 10000000) ∧
    -Real.log (9998229 / 10000000) ≤ (44279 / 250000000) := by
  have h := checkLog_sound (w := (1771 / 19998229)) (n := 12)
    (lo := (35423 / 200000000)) (hi := (44279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998229) = 1/(9998229 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3754 : Bounds (-44279 / 250000000) (-35423 / 200000000) (Real.log (9998229 / 10000000)) := by
  have h := reflection_log_3754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3755_neg : (17036541 / 200000000) ≤ -Real.log (250000 / 272229) ∧
    -Real.log (250000 / 272229) ≤ (42591353 / 500000000) := by
  have h := checkLog_sound (w := (22229 / 522229)) (n := 12)
    (lo := (17036541 / 200000000)) (hi := (42591353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272229 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272229 / 250000) = 1/(250000 / 272229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3755 : Bounds (17036541 / 200000000) (42591353 / 500000000) (Real.log (272229 / 250000)) := by
  have h := reflection_log_3755_neg
  have he : Real.log (272229 / 250000) = -Real.log (250000 / 272229) := by
    rw [show ((272229 / 250000) : ℝ) = ((250000 / 272229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3756_neg : (93120179 / 1000000000) ≤ -Real.log (227771 / 250000) ∧
    -Real.log (227771 / 250000) ≤ (4656009 / 50000000) := by
  have h := checkLog_sound (w := (22229 / 477771)) (n := 12)
    (lo := (93120179 / 1000000000)) (hi := (4656009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227771) = 1/(227771 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3756 : Bounds (-4656009 / 50000000) (-93120179 / 1000000000) (Real.log (227771 / 250000)) := by
  have h := reflection_log_3756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3757_neg : (42696033 / 500000000) ≤ -Real.log (125000 / 136143) ∧
    -Real.log (125000 / 136143) ≤ (85392067 / 1000000000) := by
  have h := checkLog_sound (w := (11143 / 261143)) (n := 12)
    (lo := (42696033 / 500000000)) (hi := (85392067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136143 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136143 / 125000) = 1/(125000 / 136143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3757 : Bounds (42696033 / 500000000) (85392067 / 1000000000) (Real.log (136143 / 125000)) := by
  have h := reflection_log_3757_neg
  have he : Real.log (136143 / 125000) = -Real.log (125000 / 136143) := by
    rw [show ((136143 / 125000) : ℝ) = ((125000 / 136143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3758_neg : (46685231 / 500000000) ≤ -Real.log (113857 / 125000) ∧
    -Real.log (113857 / 125000) ≤ (93370463 / 1000000000) := by
  have h := checkLog_sound (w := (11143 / 238857)) (n := 12)
    (lo := (46685231 / 500000000)) (hi := (93370463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113857) = 1/(113857 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3758 : Bounds (-93370463 / 1000000000) (-46685231 / 500000000) (Real.log (113857 / 125000)) := by
  have h := reflection_log_3758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3759_neg : (1595679 / 200000000) ≤ -Real.log (15500833551 / 15625000000) ∧
    -Real.log (15500833551 / 15625000000) ≤ (1994599 / 250000000) := by
  have h := checkLog_sound (w := (124166449 / 31125833551)) (n := 12)
    (lo := (1595679 / 200000000)) (hi := (1994599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15500833551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15500833551) = 1/(15500833551 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3759 : Bounds (-1994599 / 250000000) (-1595679 / 200000000) (Real.log (15500833551 / 15625000000)) := by
  have h := reflection_log_3759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3760_neg : (7937473 / 1000000000) ≤ -Real.log (62005871559 / 62500000000) ∧
    -Real.log (62005871559 / 62500000000) ≤ (3968737 / 500000000) := by
  have h := checkLog_sound (w := (494128441 / 124505871559)) (n := 12)
    (lo := (7937473 / 1000000000)) (hi := (3968737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62005871559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62005871559) = 1/(62005871559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3760 : Bounds (-3968737 / 500000000) (-7937473 / 1000000000) (Real.log (62005871559 / 62500000000)) := by
  have h := reflection_log_3760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3761_neg : (35660577 / 200000000) ≤ -Real.log (500000000000 / 597593635713) ∧
    -Real.log (500000000000 / 597593635713) ≤ (89151443 / 500000000) := by
  have h := checkLog_sound (w := (97593635713 / 1097593635713)) (n := 12)
    (lo := (35660577 / 200000000)) (hi := (89151443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597593635713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597593635713 / 500000000000) = 1/(500000000000 / 597593635713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3761 : Bounds (35660577 / 200000000) (89151443 / 500000000) (Real.log (597593635713 / 500000000000)) := by
  have h := reflection_log_3761_neg
  have he : Real.log (597593635713 / 500000000000) = -Real.log (500000000000 / 597593635713) := by
    rw [show ((597593635713 / 500000000000) : ℝ) = ((500000000000 / 597593635713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3762_neg : (5586329 / 31250000) ≤ -Real.log (125000000000 / 149467094689) ∧
    -Real.log (125000000000 / 149467094689) ≤ (178762529 / 1000000000) := by
  have h := checkLog_sound (w := (24467094689 / 274467094689)) (n := 12)
    (lo := (5586329 / 31250000)) (hi := (178762529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149467094689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149467094689 / 125000000000) = 1/(125000000000 / 149467094689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3762 : Bounds (5586329 / 31250000) (178762529 / 1000000000) (Real.log (149467094689 / 125000000000)) := by
  have h := reflection_log_3762_neg
  have he : Real.log (149467094689 / 125000000000) = -Real.log (125000000000 / 149467094689) := by
    rw [show ((149467094689 / 125000000000) : ℝ) = ((125000000000 / 149467094689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3763_neg : (178883953 / 500000000) ≤ -Real.log (20000000000 / 28602673147) ∧
    -Real.log (20000000000 / 28602673147) ≤ (357767907 / 1000000000) := by
  have h := checkLog_sound (w := (8602673147 / 48602673147)) (n := 12)
    (lo := (178883953 / 500000000)) (hi := (357767907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28602673147 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28602673147 / 20000000000) = 1/(20000000000 / 28602673147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3763 : Bounds (178883953 / 500000000) (357767907 / 1000000000) (Real.log (28602673147 / 20000000000)) := by
  have h := reflection_log_3763_neg
  have he : Real.log (28602673147 / 20000000000) = -Real.log (20000000000 / 28602673147) := by
    rw [show ((28602673147 / 20000000000) : ℝ) = ((20000000000 / 28602673147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3764_neg : (178987189 / 500000000) ≤ -Real.log (500000000000 / 715214485357) ∧
    -Real.log (500000000000 / 715214485357) ≤ (357974379 / 1000000000) := by
  have h := checkLog_sound (w := (215214485357 / 1215214485357)) (n := 12)
    (lo := (178987189 / 500000000)) (hi := (357974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715214485357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715214485357 / 500000000000) = 1/(500000000000 / 715214485357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3764 : Bounds (178987189 / 500000000) (357974379 / 1000000000) (Real.log (715214485357 / 500000000000)) := by
  have h := reflection_log_3764_neg
  have he : Real.log (715214485357 / 500000000000) = -Real.log (500000000000 / 715214485357) := by
    rw [show ((715214485357 / 500000000000) : ℝ) = ((500000000000 / 715214485357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3765_neg : (163138737 / 1000000000) ≤ -Real.log (2500 / 2943) ∧
    -Real.log (2500 / 2943) ≤ (81569369 / 500000000) := by
  have h := checkLog_sound (w := (443 / 5443)) (n := 12)
    (lo := (163138737 / 1000000000)) (hi := (81569369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2943 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2943 / 2500) = 1/(2500 / 2943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3765 : Bounds (163138737 / 1000000000) (81569369 / 500000000) (Real.log (2943 / 2500)) := by
  have h := reflection_log_3765_neg
  have he : Real.log (2943 / 2500) = -Real.log (2500 / 2943) := by
    rw [show ((2943 / 2500) : ℝ) = ((2500 / 2943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3766_neg : (195042121 / 1000000000) ≤ -Real.log (2057 / 2500) ∧
    -Real.log (2057 / 2500) ≤ (97521061 / 500000000) := by
  have h := checkLog_sound (w := (443 / 4557)) (n := 12)
    (lo := (195042121 / 1000000000)) (hi := (97521061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2057) = 1/(2057 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3766 : Bounds (-97521061 / 500000000) (-195042121 / 1000000000) (Real.log (2057 / 2500)) := by
  have h := reflection_log_3766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3767_neg : (5537 / 31250000) ≤ -Real.log (2500000 / 2500443) ∧
    -Real.log (2500000 / 2500443) ≤ (35437 / 200000000) := by
  have h := checkLog_sound (w := (443 / 5000443)) (n := 12)
    (lo := (5537 / 31250000)) (hi := (35437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500443 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500443 / 2500000) = 1/(2500000 / 2500443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3767 : Bounds (5537 / 31250000) (35437 / 200000000) (Real.log (2500443 / 2500000)) := by
  have h := reflection_log_3767_neg
  have he : Real.log (2500443 / 2500000) = -Real.log (2500000 / 2500443) := by
    rw [show ((2500443 / 2500000) : ℝ) = ((2500000 / 2500443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3768_neg : (35443 / 200000000) ≤ -Real.log (2499557 / 2500000) ∧
    -Real.log (2499557 / 2500000) ≤ (2769 / 15625000) := by
  have h := checkLog_sound (w := (443 / 4999557)) (n := 12)
    (lo := (35443 / 200000000)) (hi := (2769 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499557) = 1/(2499557 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3768 : Bounds (-2769 / 15625000) (-35443 / 200000000) (Real.log (2499557 / 2500000)) := by
  have h := reflection_log_3768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3769_neg : (4261477 / 50000000) ≤ -Real.log (1000000 / 1088967) ∧
    -Real.log (1000000 / 1088967) ≤ (85229541 / 1000000000) := by
  have h := checkLog_sound (w := (88967 / 2088967)) (n := 12)
    (lo := (4261477 / 50000000)) (hi := (85229541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088967 / 1000000) = 1/(1000000 / 1088967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3769 : Bounds (4261477 / 50000000) (85229541 / 1000000000) (Real.log (1088967 / 1000000)) := by
  have h := reflection_log_3769_neg
  have he : Real.log (1088967 / 1000000) = -Real.log (1000000 / 1088967) := by
    rw [show ((1088967 / 1000000) : ℝ) = ((1000000 / 1088967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3770_neg : (46588079 / 500000000) ≤ -Real.log (911033 / 1000000) ∧
    -Real.log (911033 / 1000000) ≤ (93176159 / 1000000000) := by
  have h := checkLog_sound (w := (88967 / 1911033)) (n := 12)
    (lo := (46588079 / 500000000)) (hi := (93176159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911033) = 1/(911033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3770 : Bounds (-93176159 / 1000000000) (-46588079 / 500000000) (Real.log (911033 / 1000000)) := by
  have h := reflection_log_3770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3771_neg : (85438891 / 1000000000) ≤ -Real.log (200000 / 217839) ∧
    -Real.log (200000 / 217839) ≤ (21359723 / 250000000) := by
  have h := checkLog_sound (w := (17839 / 417839)) (n := 12)
    (lo := (85438891 / 1000000000)) (hi := (21359723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217839 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217839 / 200000) = 1/(200000 / 217839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3771 : Bounds (85438891 / 1000000000) (21359723 / 250000000) (Real.log (217839 / 200000)) := by
  have h := reflection_log_3771_neg
  have he : Real.log (217839 / 200000) = -Real.log (200000 / 217839) := by
    rw [show ((217839 / 200000) : ℝ) = ((200000 / 217839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3772_neg : (18685291 / 200000000) ≤ -Real.log (182161 / 200000) ∧
    -Real.log (182161 / 200000) ≤ (11678307 / 125000000) := by
  have h := checkLog_sound (w := (17839 / 382161)) (n := 12)
    (lo := (18685291 / 200000000)) (hi := (11678307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182161) = 1/(182161 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3772 : Bounds (-11678307 / 125000000) (-18685291 / 200000000) (Real.log (182161 / 200000)) := by
  have h := reflection_log_3772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3773_neg : (7987563 / 1000000000) ≤ -Real.log (39681770079 / 40000000000) ∧
    -Real.log (39681770079 / 40000000000) ≤ (1996891 / 250000000) := by
  have h := checkLog_sound (w := (318229921 / 79681770079)) (n := 12)
    (lo := (7987563 / 1000000000)) (hi := (1996891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39681770079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39681770079) = 1/(39681770079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3773 : Bounds (-1996891 / 250000000) (-7987563 / 1000000000) (Real.log (39681770079 / 40000000000)) := by
  have h := reflection_log_3773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3774_neg : (7946617 / 1000000000) ≤ -Real.log (992084872911 / 1000000000000) ∧
    -Real.log (992084872911 / 1000000000000) ≤ (3973309 / 500000000) := by
  have h := checkLog_sound (w := (7915127089 / 1992084872911)) (n := 12)
    (lo := (7946617 / 1000000000)) (hi := (3973309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992084872911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992084872911) = 1/(992084872911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3774 : Bounds (-3973309 / 500000000) (-7946617 / 1000000000) (Real.log (992084872911 / 1000000000000)) := by
  have h := reflection_log_3774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3775_neg : (89202849 / 500000000) ≤ -Real.log (500000000000 / 597655079453) ∧
    -Real.log (500000000000 / 597655079453) ≤ (178405699 / 1000000000) := by
  have h := checkLog_sound (w := (97655079453 / 1097655079453)) (n := 12)
    (lo := (89202849 / 500000000)) (hi := (178405699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597655079453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597655079453 / 500000000000) = 1/(500000000000 / 597655079453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3775 : Bounds (89202849 / 500000000) (178405699 / 1000000000) (Real.log (597655079453 / 500000000000)) := by
  have h := reflection_log_3775_neg
  have he : Real.log (597655079453 / 500000000000) = -Real.log (500000000000 / 597655079453) := by
    rw [show ((597655079453 / 500000000000) : ℝ) = ((500000000000 / 597655079453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0059 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3776_neg : (89432673 / 500000000) ≤ -Real.log (250000000000 / 298964926631) ∧
    -Real.log (250000000000 / 298964926631) ≤ (178865347 / 1000000000) := by
  have h := checkLog_sound (w := (48964926631 / 548964926631)) (n := 12)
    (lo := (89432673 / 500000000)) (hi := (178865347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298964926631 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298964926631 / 250000000000) = 1/(250000000000 / 298964926631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3776 : Bounds (89432673 / 500000000) (178865347 / 1000000000) (Real.log (298964926631 / 250000000000)) := by
  have h := reflection_log_3776_neg
  have he : Real.log (298964926631 / 250000000000) = -Real.log (250000000000 / 298964926631) := by
    rw [show ((298964926631 / 250000000000) : ℝ) = ((250000000000 / 298964926631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3777_neg : (178987189 / 500000000) ≤ -Real.log (125000000000 / 178803621339) ∧
    -Real.log (125000000000 / 178803621339) ≤ (357974379 / 1000000000) := by
  have h := checkLog_sound (w := (53803621339 / 303803621339)) (n := 12)
    (lo := (178987189 / 500000000)) (hi := (357974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178803621339 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178803621339 / 125000000000) = 1/(125000000000 / 178803621339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3777 : Bounds (178987189 / 500000000) (357974379 / 1000000000) (Real.log (178803621339 / 125000000000)) := by
  have h := reflection_log_3777_neg
  have he : Real.log (178803621339 / 125000000000) = -Real.log (125000000000 / 178803621339) := by
    rw [show ((178803621339 / 125000000000) : ℝ) = ((125000000000 / 178803621339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3778_neg : (179090429 / 500000000) ≤ -Real.log (50000000000 / 71536217793) ∧
    -Real.log (50000000000 / 71536217793) ≤ (358180859 / 1000000000) := by
  have h := checkLog_sound (w := (21536217793 / 121536217793)) (n := 12)
    (lo := (179090429 / 500000000)) (hi := (358180859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71536217793 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71536217793 / 50000000000) = 1/(50000000000 / 71536217793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3778 : Bounds (179090429 / 500000000) (358180859 / 1000000000) (Real.log (71536217793 / 50000000000)) := by
  have h := reflection_log_3778_neg
  have he : Real.log (71536217793 / 50000000000) = -Real.log (50000000000 / 71536217793) := by
    rw [show ((71536217793 / 50000000000) : ℝ) = ((50000000000 / 71536217793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3779_neg : (163223681 / 1000000000) ≤ -Real.log (10000 / 11773) ∧
    -Real.log (10000 / 11773) ≤ (81611841 / 500000000) := by
  have h := checkLog_sound (w := (1773 / 21773)) (n := 12)
    (lo := (163223681 / 1000000000)) (hi := (81611841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11773 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11773 / 10000) = 1/(10000 / 11773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3779 : Bounds (163223681 / 1000000000) (81611841 / 500000000) (Real.log (11773 / 10000)) := by
  have h := reflection_log_3779_neg
  have he : Real.log (11773 / 10000) = -Real.log (10000 / 11773) := by
    rw [show ((11773 / 10000) : ℝ) = ((10000 / 11773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3780_neg : (12197729 / 62500000) ≤ -Real.log (8227 / 10000) ∧
    -Real.log (8227 / 10000) ≤ (39032733 / 200000000) := by
  have h := checkLog_sound (w := (1773 / 18227)) (n := 12)
    (lo := (12197729 / 62500000)) (hi := (39032733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8227) = 1/(8227 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3780 : Bounds (-39032733 / 200000000) (-12197729 / 62500000) (Real.log (8227 / 10000)) := by
  have h := reflection_log_3780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3781_neg : (44321 / 250000000) ≤ -Real.log (10000000 / 10001773) ∧
    -Real.log (10000000 / 10001773) ≤ (35457 / 200000000) := by
  have h := checkLog_sound (w := (1773 / 20001773)) (n := 12)
    (lo := (44321 / 250000000)) (hi := (35457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001773 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001773 / 10000000) = 1/(10000000 / 10001773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3781 : Bounds (44321 / 250000000) (35457 / 200000000) (Real.log (10001773 / 10000000)) := by
  have h := reflection_log_3781_neg
  have he : Real.log (10001773 / 10000000) = -Real.log (10000000 / 10001773) := by
    rw [show ((10001773 / 10000000) : ℝ) = ((10000000 / 10001773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3782_neg : (35463 / 200000000) ≤ -Real.log (9998227 / 10000000) ∧
    -Real.log (9998227 / 10000000) ≤ (44329 / 250000000) := by
  have h := checkLog_sound (w := (1773 / 19998227)) (n := 12)
    (lo := (35463 / 200000000)) (hi := (44329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998227) = 1/(9998227 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3782 : Bounds (-44329 / 250000000) (-35463 / 200000000) (Real.log (9998227 / 10000000)) := by
  have h := reflection_log_3782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3783_neg : (21319093 / 250000000) ≤ -Real.log (500000 / 544509) ∧
    -Real.log (500000 / 544509) ≤ (85276373 / 1000000000) := by
  have h := checkLog_sound (w := (44509 / 1044509)) (n := 12)
    (lo := (21319093 / 250000000)) (hi := (85276373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544509 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544509 / 500000) = 1/(500000 / 544509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3783 : Bounds (21319093 / 250000000) (85276373 / 1000000000) (Real.log (544509 / 500000)) := by
  have h := reflection_log_3783_neg
  have he : Real.log (544509 / 500000) = -Real.log (500000 / 544509) := by
    rw [show ((544509 / 500000) : ℝ) = ((500000 / 544509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3784_neg : (4661607 / 50000000) ≤ -Real.log (455491 / 500000) ∧
    -Real.log (455491 / 500000) ≤ (93232141 / 1000000000) := by
  have h := checkLog_sound (w := (44509 / 955491)) (n := 12)
    (lo := (4661607 / 50000000)) (hi := (93232141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455491) = 1/(455491 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3784 : Bounds (-93232141 / 1000000000) (-4661607 / 50000000) (Real.log (455491 / 500000)) := by
  have h := reflection_log_3784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3785_neg : (85485713 / 1000000000) ≤ -Real.log (500000 / 544623) ∧
    -Real.log (500000 / 544623) ≤ (42742857 / 500000000) := by
  have h := checkLog_sound (w := (44623 / 1044623)) (n := 12)
    (lo := (85485713 / 1000000000)) (hi := (42742857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544623 / 500000) = 1/(500000 / 544623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3785 : Bounds (85485713 / 1000000000) (42742857 / 500000000) (Real.log (544623 / 500000)) := by
  have h := reflection_log_3785_neg
  have he : Real.log (544623 / 500000) = -Real.log (500000 / 544623) := by
    rw [show ((544623 / 500000) : ℝ) = ((500000 / 544623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3786_neg : (93482451 / 1000000000) ≤ -Real.log (455377 / 500000) ∧
    -Real.log (455377 / 500000) ≤ (23370613 / 250000000) := by
  have h := checkLog_sound (w := (44623 / 955377)) (n := 12)
    (lo := (93482451 / 1000000000)) (hi := (23370613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455377) = 1/(455377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3786 : Bounds (-23370613 / 250000000) (-93482451 / 1000000000) (Real.log (455377 / 500000)) := by
  have h := reflection_log_3786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3787_neg : (7996737 / 1000000000) ≤ -Real.log (248008787871 / 250000000000) ∧
    -Real.log (248008787871 / 250000000000) ≤ (3998369 / 500000000) := by
  have h := checkLog_sound (w := (1991212129 / 498008787871)) (n := 12)
    (lo := (7996737 / 1000000000)) (hi := (3998369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248008787871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248008787871) = 1/(248008787871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3787 : Bounds (-3998369 / 500000000) (-7996737 / 1000000000) (Real.log (248008787871 / 250000000000)) := by
  have h := reflection_log_3787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3788_neg : (7955767 / 1000000000) ≤ -Real.log (248018948919 / 250000000000) ∧
    -Real.log (248018948919 / 250000000000) ≤ (994471 / 125000000) := by
  have h := checkLog_sound (w := (1981051081 / 498018948919)) (n := 12)
    (lo := (7955767 / 1000000000)) (hi := (994471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248018948919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248018948919) = 1/(248018948919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3788 : Bounds (-994471 / 125000000) (-7955767 / 1000000000) (Real.log (248018948919 / 250000000000)) := by
  have h := reflection_log_3788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3789_neg : (178508513 / 1000000000) ≤ -Real.log (250000000000 / 298858265037) ∧
    -Real.log (250000000000 / 298858265037) ≤ (89254257 / 500000000) := by
  have h := checkLog_sound (w := (48858265037 / 548858265037)) (n := 12)
    (lo := (178508513 / 1000000000)) (hi := (89254257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298858265037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298858265037 / 250000000000) = 1/(250000000000 / 298858265037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3789 : Bounds (178508513 / 1000000000) (89254257 / 500000000) (Real.log (298858265037 / 250000000000)) := by
  have h := reflection_log_3789_neg
  have he : Real.log (298858265037 / 250000000000) = -Real.log (250000000000 / 298858265037) := by
    rw [show ((298858265037 / 250000000000) : ℝ) = ((250000000000 / 298858265037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3790_neg : (44742041 / 250000000) ≤ -Real.log (500000000000 / 597991334653) ∧
    -Real.log (500000000000 / 597991334653) ≤ (35793633 / 200000000) := by
  have h := checkLog_sound (w := (97991334653 / 1097991334653)) (n := 12)
    (lo := (44742041 / 250000000)) (hi := (35793633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597991334653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597991334653 / 500000000000) = 1/(500000000000 / 597991334653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3790 : Bounds (44742041 / 250000000) (35793633 / 200000000) (Real.log (597991334653 / 500000000000)) := by
  have h := reflection_log_3790_neg
  have he : Real.log (597991334653 / 500000000000) = -Real.log (500000000000 / 597991334653) := by
    rw [show ((597991334653 / 500000000000) : ℝ) = ((500000000000 / 597991334653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3791_neg : (179090429 / 500000000) ≤ -Real.log (500000000000 / 715362177929) ∧
    -Real.log (500000000000 / 715362177929) ≤ (358180859 / 1000000000) := by
  have h := checkLog_sound (w := (215362177929 / 1215362177929)) (n := 12)
    (lo := (179090429 / 500000000)) (hi := (358180859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715362177929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715362177929 / 500000000000) = 1/(500000000000 / 715362177929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3791 : Bounds (179090429 / 500000000) (358180859 / 1000000000) (Real.log (715362177929 / 500000000000)) := by
  have h := reflection_log_3791_neg
  have he : Real.log (715362177929 / 500000000000) = -Real.log (500000000000 / 715362177929) := by
    rw [show ((715362177929 / 500000000000) : ℝ) = ((500000000000 / 715362177929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3792_neg : (71677469 / 200000000) ≤ -Real.log (250000000000 / 357754953203) ∧
    -Real.log (250000000000 / 357754953203) ≤ (179193673 / 500000000) := by
  have h := checkLog_sound (w := (107754953203 / 607754953203)) (n := 12)
    (lo := (71677469 / 200000000)) (hi := (179193673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357754953203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357754953203 / 250000000000) = 1/(250000000000 / 357754953203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3792 : Bounds (71677469 / 200000000) (179193673 / 500000000) (Real.log (357754953203 / 250000000000)) := by
  have h := reflection_log_3792_neg
  have he : Real.log (357754953203 / 250000000000) = -Real.log (250000000000 / 357754953203) := by
    rw [show ((357754953203 / 250000000000) : ℝ) = ((250000000000 / 357754953203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3793_neg : (163308617 / 1000000000) ≤ -Real.log (5000 / 5887) ∧
    -Real.log (5000 / 5887) ≤ (81654309 / 500000000) := by
  have h := checkLog_sound (w := (887 / 10887)) (n := 12)
    (lo := (163308617 / 1000000000)) (hi := (81654309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5887 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5887 / 5000) = 1/(5000 / 5887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3793 : Bounds (163308617 / 1000000000) (81654309 / 500000000) (Real.log (5887 / 5000)) := by
  have h := reflection_log_3793_neg
  have he : Real.log (5887 / 5000) = -Real.log (5000 / 5887) := by
    rw [show ((5887 / 5000) : ℝ) = ((5000 / 5887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3794_neg : (195285223 / 1000000000) ≤ -Real.log (4113 / 5000) ∧
    -Real.log (4113 / 5000) ≤ (24410653 / 125000000) := by
  have h := checkLog_sound (w := (887 / 9113)) (n := 12)
    (lo := (195285223 / 1000000000)) (hi := (24410653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4113) = 1/(4113 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3794 : Bounds (-24410653 / 125000000) (-195285223 / 1000000000) (Real.log (4113 / 5000)) := by
  have h := reflection_log_3794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3795_neg : (22173 / 125000000) ≤ -Real.log (5000000 / 5000887) ∧
    -Real.log (5000000 / 5000887) ≤ (35477 / 200000000) := by
  have h := checkLog_sound (w := (887 / 10000887)) (n := 12)
    (lo := (22173 / 125000000)) (hi := (35477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000887 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000887 / 5000000) = 1/(5000000 / 5000887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3795 : Bounds (22173 / 125000000) (35477 / 200000000) (Real.log (5000887 / 5000000)) := by
  have h := reflection_log_3795_neg
  have he : Real.log (5000887 / 5000000) = -Real.log (5000000 / 5000887) := by
    rw [show ((5000887 / 5000000) : ℝ) = ((5000000 / 5000887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3796_neg : (35483 / 200000000) ≤ -Real.log (4999113 / 5000000) ∧
    -Real.log (4999113 / 5000000) ≤ (22177 / 125000000) := by
  have h := checkLog_sound (w := (887 / 9999113)) (n := 12)
    (lo := (35483 / 200000000)) (hi := (22177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999113) = 1/(4999113 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3796 : Bounds (-22177 / 125000000) (-35483 / 200000000) (Real.log (4999113 / 5000000)) := by
  have h := reflection_log_3796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3797_neg : (42661601 / 500000000) ≤ -Real.log (1000000 / 1089069) ∧
    -Real.log (1000000 / 1089069) ≤ (85323203 / 1000000000) := by
  have h := checkLog_sound (w := (89069 / 2089069)) (n := 12)
    (lo := (42661601 / 500000000)) (hi := (85323203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089069 / 1000000) = 1/(1000000 / 1089069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3797 : Bounds (42661601 / 500000000) (85323203 / 1000000000) (Real.log (1089069 / 1000000)) := by
  have h := reflection_log_3797_neg
  have he : Real.log (1089069 / 1000000) = -Real.log (1000000 / 1089069) := by
    rw [show ((1089069 / 1000000) : ℝ) = ((1000000 / 1089069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3798_neg : (149261 / 1600000) ≤ -Real.log (910931 / 1000000) ∧
    -Real.log (910931 / 1000000) ≤ (46644063 / 500000000) := by
  have h := checkLog_sound (w := (89069 / 1910931)) (n := 12)
    (lo := (149261 / 1600000)) (hi := (46644063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910931) = 1/(910931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3798 : Bounds (-46644063 / 500000000) (-149261 / 1600000) (Real.log (910931 / 1000000)) := by
  have h := reflection_log_3798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3799_neg : (42766267 / 500000000) ≤ -Real.log (1000000 / 1089297) ∧
    -Real.log (1000000 / 1089297) ≤ (17106507 / 200000000) := by
  have h := checkLog_sound (w := (89297 / 2089297)) (n := 12)
    (lo := (42766267 / 500000000)) (hi := (17106507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089297 / 1000000) = 1/(1000000 / 1089297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3799 : Bounds (42766267 / 500000000) (17106507 / 200000000) (Real.log (1089297 / 1000000)) := by
  have h := reflection_log_3799_neg
  have he : Real.log (1089297 / 1000000) = -Real.log (1000000 / 1089297) := by
    rw [show ((1089297 / 1000000) : ℝ) = ((1000000 / 1089297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3800_neg : (1870769 / 20000000) ≤ -Real.log (910703 / 1000000) ∧
    -Real.log (910703 / 1000000) ≤ (93538451 / 1000000000) := by
  have h := checkLog_sound (w := (89297 / 1910703)) (n := 12)
    (lo := (1870769 / 20000000)) (hi := (93538451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910703) = 1/(910703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3800 : Bounds (-93538451 / 1000000000) (-1870769 / 20000000) (Real.log (910703 / 1000000)) := by
  have h := reflection_log_3800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3801_neg : (2001479 / 250000000) ≤ -Real.log (992026045791 / 1000000000000) ∧
    -Real.log (992026045791 / 1000000000000) ≤ (8005917 / 1000000000) := by
  have h := checkLog_sound (w := (7973954209 / 1992026045791)) (n := 12)
    (lo := (2001479 / 250000000)) (hi := (8005917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992026045791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992026045791) = 1/(992026045791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3801 : Bounds (-8005917 / 1000000000) (-2001479 / 250000000) (Real.log (992026045791 / 1000000000000)) := by
  have h := reflection_log_3801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3802_neg : (3982461 / 500000000) ≤ -Real.log (992066713239 / 1000000000000) ∧
    -Real.log (992066713239 / 1000000000000) ≤ (7964923 / 1000000000) := by
  have h := checkLog_sound (w := (7933286761 / 1992066713239)) (n := 12)
    (lo := (3982461 / 500000000)) (hi := (7964923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992066713239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992066713239) = 1/(992066713239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3802 : Bounds (-7964923 / 1000000000) (-3982461 / 500000000) (Real.log (992066713239 / 1000000000000)) := by
  have h := reflection_log_3802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3803_neg : (1395401 / 7812500) ≤ -Real.log (20000000000 / 23911119503) ∧
    -Real.log (20000000000 / 23911119503) ≤ (178611329 / 1000000000) := by
  have h := checkLog_sound (w := (3911119503 / 43911119503)) (n := 12)
    (lo := (1395401 / 7812500)) (hi := (178611329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23911119503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23911119503 / 20000000000) = 1/(20000000000 / 23911119503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3803 : Bounds (1395401 / 7812500) (178611329 / 1000000000) (Real.log (23911119503 / 20000000000)) := by
  have h := reflection_log_3803_neg
  have he : Real.log (23911119503 / 20000000000) = -Real.log (20000000000 / 23911119503) := by
    rw [show ((23911119503 / 20000000000) : ℝ) = ((20000000000 / 23911119503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3804_neg : (22383873 / 125000000) ≤ -Real.log (50000000000 / 59805282293) ∧
    -Real.log (50000000000 / 59805282293) ≤ (35814197 / 200000000) := by
  have h := checkLog_sound (w := (9805282293 / 109805282293)) (n := 12)
    (lo := (22383873 / 125000000)) (hi := (35814197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59805282293 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59805282293 / 50000000000) = 1/(50000000000 / 59805282293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3804 : Bounds (22383873 / 125000000) (35814197 / 200000000) (Real.log (59805282293 / 50000000000)) := by
  have h := reflection_log_3804_neg
  have he : Real.log (59805282293 / 50000000000) = -Real.log (50000000000 / 59805282293) := by
    rw [show ((59805282293 / 50000000000) : ℝ) = ((50000000000 / 59805282293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3805_neg : (71677469 / 200000000) ≤ -Real.log (100000000000 / 143101981281) ∧
    -Real.log (100000000000 / 143101981281) ≤ (179193673 / 500000000) := by
  have h := checkLog_sound (w := (43101981281 / 243101981281)) (n := 12)
    (lo := (71677469 / 200000000)) (hi := (179193673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143101981281 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143101981281 / 100000000000) = 1/(100000000000 / 143101981281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3805 : Bounds (71677469 / 200000000) (179193673 / 500000000) (Real.log (143101981281 / 100000000000)) := by
  have h := reflection_log_3805_neg
  have he : Real.log (143101981281 / 100000000000) = -Real.log (100000000000 / 143101981281) := by
    rw [show ((143101981281 / 100000000000) : ℝ) = ((100000000000 / 143101981281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3806_neg : (4482423 / 12500000) ≤ -Real.log (1250000000 / 1789144177) ∧
    -Real.log (1250000000 / 1789144177) ≤ (358593841 / 1000000000) := by
  have h := checkLog_sound (w := (539144177 / 3039144177)) (n := 12)
    (lo := (4482423 / 12500000)) (hi := (358593841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789144177 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789144177 / 1250000000) = 1/(1250000000 / 1789144177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3806 : Bounds (4482423 / 12500000) (358593841 / 1000000000) (Real.log (1789144177 / 1250000000)) := by
  have h := reflection_log_3806_neg
  have he : Real.log (1789144177 / 1250000000) = -Real.log (1250000000 / 1789144177) := by
    rw [show ((1789144177 / 1250000000) : ℝ) = ((1250000000 / 1789144177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3807_neg : (81696773 / 500000000) ≤ -Real.log (400 / 471) ∧
    -Real.log (400 / 471) ≤ (163393547 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 871)) (n := 12)
    (lo := (81696773 / 500000000)) (hi := (163393547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 400) = 1/(400 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3807 : Bounds (81696773 / 500000000) (163393547 / 1000000000) (Real.log (471 / 400)) := by
  have h := reflection_log_3807_neg
  have he : Real.log (471 / 400) = -Real.log (400 / 471) := by
    rw [show ((471 / 400) : ℝ) = ((400 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3808_neg : (48851699 / 250000000) ≤ -Real.log (329 / 400) ∧
    -Real.log (329 / 400) ≤ (195406797 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 729)) (n := 12)
    (lo := (48851699 / 250000000)) (hi := (195406797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 329) = 1/(329 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3808 : Bounds (-195406797 / 1000000000) (-48851699 / 250000000) (Real.log (329 / 400)) := by
  have h := reflection_log_3808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3809_neg : (44371 / 250000000) ≤ -Real.log (400000 / 400071) ∧
    -Real.log (400000 / 400071) ≤ (35497 / 200000000) := by
  have h := checkLog_sound (w := (71 / 800071)) (n := 12)
    (lo := (44371 / 250000000)) (hi := (35497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400071 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400071 / 400000) = 1/(400000 / 400071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3809 : Bounds (44371 / 250000000) (35497 / 200000000) (Real.log (400071 / 400000)) := by
  have h := reflection_log_3809_neg
  have he : Real.log (400071 / 400000) = -Real.log (400000 / 400071) := by
    rw [show ((400071 / 400000) : ℝ) = ((400000 / 400071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3810_neg : (35503 / 200000000) ≤ -Real.log (399929 / 400000) ∧
    -Real.log (399929 / 400000) ≤ (44379 / 250000000) := by
  have h := checkLog_sound (w := (71 / 799929)) (n := 12)
    (lo := (35503 / 200000000)) (hi := (44379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399929) = 1/(399929 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3810 : Bounds (-44379 / 250000000) (-35503 / 200000000) (Real.log (399929 / 400000)) := by
  have h := reflection_log_3810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3811_neg : (10671139 / 125000000) ≤ -Real.log (1000000 / 1089119) ∧
    -Real.log (1000000 / 1089119) ≤ (85369113 / 1000000000) := by
  have h := checkLog_sound (w := (89119 / 2089119)) (n := 12)
    (lo := (10671139 / 125000000)) (hi := (85369113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089119 / 1000000) = 1/(1000000 / 1089119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3811 : Bounds (10671139 / 125000000) (85369113 / 1000000000) (Real.log (1089119 / 1000000)) := by
  have h := reflection_log_3811_neg
  have he : Real.log (1089119 / 1000000) = -Real.log (1000000 / 1089119) := by
    rw [show ((1089119 / 1000000) : ℝ) = ((1000000 / 1089119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3812_neg : (18668603 / 200000000) ≤ -Real.log (910881 / 1000000) ∧
    -Real.log (910881 / 1000000) ≤ (11667877 / 125000000) := by
  have h := checkLog_sound (w := (89119 / 1910881)) (n := 12)
    (lo := (18668603 / 200000000)) (hi := (11667877 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910881) = 1/(910881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3812 : Bounds (-11667877 / 125000000) (-18668603 / 200000000) (Real.log (910881 / 1000000)) := by
  have h := reflection_log_3812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3813_neg : (10697419 / 125000000) ≤ -Real.log (250000 / 272337) ∧
    -Real.log (250000 / 272337) ≤ (85579353 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 522337)) (n := 12)
    (lo := (10697419 / 125000000)) (hi := (85579353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272337 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272337 / 250000) = 1/(250000 / 272337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3813 : Bounds (10697419 / 125000000) (85579353 / 1000000000) (Real.log (272337 / 250000)) := by
  have h := reflection_log_3813_neg
  have he : Real.log (272337 / 250000) = -Real.log (250000 / 272337) := by
    rw [show ((272337 / 250000) : ℝ) = ((250000 / 272337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3814_neg : (23398613 / 250000000) ≤ -Real.log (227663 / 250000) ∧
    -Real.log (227663 / 250000) ≤ (93594453 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 477663)) (n := 12)
    (lo := (23398613 / 250000000)) (hi := (93594453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227663) = 1/(227663 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3814 : Bounds (-93594453 / 1000000000) (-23398613 / 250000000) (Real.log (227663 / 250000)) := by
  have h := reflection_log_3814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3815_neg : (80151 / 10000000) ≤ -Real.log (62001058431 / 62500000000) ∧
    -Real.log (62001058431 / 62500000000) ≤ (8015101 / 1000000000) := by
  have h := checkLog_sound (w := (498941569 / 124501058431)) (n := 12)
    (lo := (80151 / 10000000)) (hi := (8015101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62001058431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62001058431) = 1/(62001058431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3815 : Bounds (-8015101 / 1000000000) (-80151 / 10000000) (Real.log (62001058431 / 62500000000)) := by
  have h := reflection_log_3815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3816_neg : (7973903 / 1000000000) ≤ -Real.log (992057803839 / 1000000000000) ∧
    -Real.log (992057803839 / 1000000000000) ≤ (498369 / 62500000) := by
  have h := checkLog_sound (w := (7942196161 / 1992057803839)) (n := 12)
    (lo := (7973903 / 1000000000)) (hi := (498369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992057803839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992057803839) = 1/(992057803839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3816 : Bounds (-498369 / 62500000) (-7973903 / 1000000000) (Real.log (992057803839 / 1000000000000)) := by
  have h := reflection_log_3816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3817_neg : (2792377 / 15625000) ≤ -Real.log (125000000000 / 149459561677) ∧
    -Real.log (125000000000 / 149459561677) ≤ (178712129 / 1000000000) := by
  have h := checkLog_sound (w := (24459561677 / 274459561677)) (n := 12)
    (lo := (2792377 / 15625000)) (hi := (178712129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149459561677 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149459561677 / 125000000000) = 1/(125000000000 / 149459561677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3817 : Bounds (2792377 / 15625000) (178712129 / 1000000000) (Real.log (149459561677 / 125000000000)) := by
  have h := reflection_log_3817_neg
  have he : Real.log (149459561677 / 125000000000) = -Real.log (125000000000 / 149459561677) := by
    rw [show ((149459561677 / 125000000000) : ℝ) = ((125000000000 / 149459561677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3818_neg : (44793451 / 250000000) ≤ -Real.log (500000000000 / 598114318093) ∧
    -Real.log (500000000000 / 598114318093) ≤ (35834761 / 200000000) := by
  have h := checkLog_sound (w := (98114318093 / 1098114318093)) (n := 12)
    (lo := (44793451 / 250000000)) (hi := (35834761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598114318093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598114318093 / 500000000000) = 1/(500000000000 / 598114318093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3818 : Bounds (44793451 / 250000000) (35834761 / 200000000) (Real.log (598114318093 / 500000000000)) := by
  have h := reflection_log_3818_neg
  have he : Real.log (598114318093 / 500000000000) = -Real.log (500000000000 / 598114318093) := by
    rw [show ((598114318093 / 500000000000) : ℝ) = ((500000000000 / 598114318093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3819_neg : (4482423 / 12500000) ≤ -Real.log (500000000000 / 715657670799) ∧
    -Real.log (500000000000 / 715657670799) ≤ (358593841 / 1000000000) := by
  have h := checkLog_sound (w := (215657670799 / 1215657670799)) (n := 12)
    (lo := (4482423 / 12500000)) (hi := (358593841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715657670799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715657670799 / 500000000000) = 1/(500000000000 / 715657670799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3819 : Bounds (4482423 / 12500000) (358593841 / 1000000000) (Real.log (715657670799 / 500000000000)) := by
  have h := reflection_log_3819_neg
  have he : Real.log (715657670799 / 500000000000) = -Real.log (500000000000 / 715657670799) := by
    rw [show ((715657670799 / 500000000000) : ℝ) = ((500000000000 / 715657670799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3820_neg : (358800343 / 1000000000) ≤ -Real.log (4000000000 / 5726443769) ∧
    -Real.log (4000000000 / 5726443769) ≤ (44850043 / 125000000) := by
  have h := checkLog_sound (w := (1726443769 / 9726443769)) (n := 12)
    (lo := (358800343 / 1000000000)) (hi := (44850043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5726443769 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5726443769 / 4000000000) = 1/(4000000000 / 5726443769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3820 : Bounds (358800343 / 1000000000) (44850043 / 125000000) (Real.log (5726443769 / 4000000000)) := by
  have h := reflection_log_3820_neg
  have he : Real.log (5726443769 / 4000000000) = -Real.log (4000000000 / 5726443769) := by
    rw [show ((5726443769 / 4000000000) : ℝ) = ((4000000000 / 5726443769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3821_neg : (40869617 / 250000000) ≤ -Real.log (625 / 736) ∧
    -Real.log (625 / 736) ≤ (163478469 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 1361)) (n := 12)
    (lo := (40869617 / 250000000)) (hi := (163478469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736 / 625) = 1/(625 / 736) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3821 : Bounds (40869617 / 250000000) (163478469 / 1000000000) (Real.log (736 / 625)) := by
  have h := reflection_log_3821_neg
  have he : Real.log (736 / 625) = -Real.log (625 / 736) := by
    rw [show ((736 / 625) : ℝ) = ((625 / 736) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3822_neg : (3055131 / 15625000) ≤ -Real.log (514 / 625) ∧
    -Real.log (514 / 625) ≤ (39105677 / 200000000) := by
  have h := checkLog_sound (w := (111 / 1139)) (n := 12)
    (lo := (3055131 / 15625000)) (hi := (39105677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 514) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 514) = 1/(514 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3822 : Bounds (-39105677 / 200000000) (-3055131 / 15625000) (Real.log (514 / 625)) := by
  have h := reflection_log_3822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3823_neg : (11099 / 62500000) ≤ -Real.log (625000 / 625111) ∧
    -Real.log (625000 / 625111) ≤ (35517 / 200000000) := by
  have h := checkLog_sound (w := (111 / 1250111)) (n := 12)
    (lo := (11099 / 62500000)) (hi := (35517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625111 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625111 / 625000) = 1/(625000 / 625111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3823 : Bounds (11099 / 62500000) (35517 / 200000000) (Real.log (625111 / 625000)) := by
  have h := reflection_log_3823_neg
  have he : Real.log (625111 / 625000) = -Real.log (625000 / 625111) := by
    rw [show ((625111 / 625000) : ℝ) = ((625000 / 625111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3824_neg : (35523 / 200000000) ≤ -Real.log (624889 / 625000) ∧
    -Real.log (624889 / 625000) ≤ (11101 / 62500000) := by
  have h := checkLog_sound (w := (111 / 1249889)) (n := 12)
    (lo := (35523 / 200000000)) (hi := (11101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624889) = 1/(624889 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3824 : Bounds (-11101 / 62500000) (-35523 / 200000000) (Real.log (624889 / 625000)) := by
  have h := reflection_log_3824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3825_neg : (42707969 / 500000000) ≤ -Real.log (100000 / 108917) ∧
    -Real.log (100000 / 108917) ≤ (85415939 / 1000000000) := by
  have h := checkLog_sound (w := (8917 / 208917)) (n := 12)
    (lo := (42707969 / 500000000)) (hi := (85415939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108917 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108917 / 100000) = 1/(100000 / 108917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3825 : Bounds (42707969 / 500000000) (85415939 / 1000000000) (Real.log (108917 / 100000)) := by
  have h := reflection_log_3825_neg
  have he : Real.log (108917 / 100000) = -Real.log (100000 / 108917) := by
    rw [show ((108917 / 100000) : ℝ) = ((100000 / 108917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3826_neg : (93399007 / 1000000000) ≤ -Real.log (91083 / 100000) ∧
    -Real.log (91083 / 100000) ≤ (2918719 / 31250000) := by
  have h := checkLog_sound (w := (8917 / 191083)) (n := 12)
    (lo := (93399007 / 1000000000)) (hi := (2918719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91083) = 1/(91083 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3826 : Bounds (-2918719 / 31250000) (-93399007 / 1000000000) (Real.log (91083 / 100000)) := by
  have h := reflection_log_3826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3827_neg : (10703271 / 125000000) ≤ -Real.log (1000000 / 1089399) ∧
    -Real.log (1000000 / 1089399) ≤ (85626169 / 1000000000) := by
  have h := checkLog_sound (w := (89399 / 2089399)) (n := 12)
    (lo := (10703271 / 125000000)) (hi := (85626169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089399 / 1000000) = 1/(1000000 / 1089399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3827 : Bounds (10703271 / 125000000) (85626169 / 1000000000) (Real.log (1089399 / 1000000)) := by
  have h := reflection_log_3827_neg
  have he : Real.log (1089399 / 1000000) = -Real.log (1000000 / 1089399) := by
    rw [show ((1089399 / 1000000) : ℝ) = ((1000000 / 1089399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3828_neg : (93650457 / 1000000000) ≤ -Real.log (910601 / 1000000) ∧
    -Real.log (910601 / 1000000) ≤ (46825229 / 500000000) := by
  have h := checkLog_sound (w := (89399 / 1910601)) (n := 12)
    (lo := (93650457 / 1000000000)) (hi := (46825229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910601) = 1/(910601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3828 : Bounds (-46825229 / 500000000) (-93650457 / 1000000000) (Real.log (910601 / 1000000)) := by
  have h := reflection_log_3828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3829_neg : (8024289 / 1000000000) ≤ -Real.log (992007818799 / 1000000000000) ∧
    -Real.log (992007818799 / 1000000000000) ≤ (802429 / 100000000) := by
  have h := checkLog_sound (w := (7992181201 / 1992007818799)) (n := 12)
    (lo := (8024289 / 1000000000)) (hi := (802429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992007818799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992007818799) = 1/(992007818799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3829 : Bounds (-802429 / 100000000) (-8024289 / 1000000000) (Real.log (992007818799 / 1000000000000)) := by
  have h := reflection_log_3829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3830_neg : (1995767 / 250000000) ≤ -Real.log (9920487111 / 10000000000) ∧
    -Real.log (9920487111 / 10000000000) ≤ (7983069 / 1000000000) := by
  have h := checkLog_sound (w := (79512889 / 19920487111)) (n := 12)
    (lo := (1995767 / 250000000)) (hi := (7983069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9920487111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9920487111) = 1/(9920487111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3830 : Bounds (-7983069 / 1000000000) (-1995767 / 250000000) (Real.log (9920487111 / 10000000000)) := by
  have h := reflection_log_3830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3831_neg : (35762989 / 200000000) ≤ -Real.log (500000000000 / 597899717839) ∧
    -Real.log (500000000000 / 597899717839) ≤ (89407473 / 500000000) := by
  have h := checkLog_sound (w := (97899717839 / 1097899717839)) (n := 12)
    (lo := (35762989 / 200000000)) (hi := (89407473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597899717839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597899717839 / 500000000000) = 1/(500000000000 / 597899717839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3831 : Bounds (35762989 / 200000000) (89407473 / 500000000) (Real.log (597899717839 / 500000000000)) := by
  have h := reflection_log_3831_neg
  have he : Real.log (597899717839 / 500000000000) = -Real.log (500000000000 / 597899717839) := by
    rw [show ((597899717839 / 500000000000) : ℝ) = ((500000000000 / 597899717839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3832_neg : (1434213 / 8000000) ≤ -Real.log (250000000000 / 299087910073) ∧
    -Real.log (250000000000 / 299087910073) ≤ (89638313 / 500000000) := by
  have h := checkLog_sound (w := (49087910073 / 549087910073)) (n := 12)
    (lo := (1434213 / 8000000)) (hi := (89638313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299087910073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299087910073 / 250000000000) = 1/(250000000000 / 299087910073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3832 : Bounds (1434213 / 8000000) (89638313 / 500000000) (Real.log (299087910073 / 250000000000)) := by
  have h := reflection_log_3832_neg
  have he : Real.log (299087910073 / 250000000000) = -Real.log (250000000000 / 299087910073) := by
    rw [show ((299087910073 / 250000000000) : ℝ) = ((250000000000 / 299087910073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3833_neg : (358800343 / 1000000000) ≤ -Real.log (125000000000 / 178951367781) ∧
    -Real.log (125000000000 / 178951367781) ≤ (44850043 / 125000000) := by
  have h := checkLog_sound (w := (53951367781 / 303951367781)) (n := 12)
    (lo := (358800343 / 1000000000)) (hi := (44850043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178951367781 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178951367781 / 125000000000) = 1/(125000000000 / 178951367781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3833 : Bounds (358800343 / 1000000000) (44850043 / 125000000) (Real.log (178951367781 / 125000000000)) := by
  have h := reflection_log_3833_neg
  have he : Real.log (178951367781 / 125000000000) = -Real.log (125000000000 / 178951367781) := by
    rw [show ((178951367781 / 125000000000) : ℝ) = ((125000000000 / 178951367781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3834_neg : (359006853 / 1000000000) ≤ -Real.log (500000000000 / 715953307393) ∧
    -Real.log (500000000000 / 715953307393) ≤ (179503427 / 500000000) := by
  have h := checkLog_sound (w := (215953307393 / 1215953307393)) (n := 12)
    (lo := (359006853 / 1000000000)) (hi := (179503427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715953307393 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715953307393 / 500000000000) = 1/(500000000000 / 715953307393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3834 : Bounds (359006853 / 1000000000) (179503427 / 500000000) (Real.log (715953307393 / 500000000000)) := by
  have h := reflection_log_3834_neg
  have he : Real.log (715953307393 / 500000000000) = -Real.log (500000000000 / 715953307393) := by
    rw [show ((715953307393 / 500000000000) : ℝ) = ((500000000000 / 715953307393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3835_neg : (163563383 / 1000000000) ≤ -Real.log (10000 / 11777) ∧
    -Real.log (10000 / 11777) ≤ (20445423 / 125000000) := by
  have h := checkLog_sound (w := (1777 / 21777)) (n := 12)
    (lo := (163563383 / 1000000000)) (hi := (20445423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11777 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11777 / 10000) = 1/(10000 / 11777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3835 : Bounds (163563383 / 1000000000) (20445423 / 125000000) (Real.log (11777 / 10000)) := by
  have h := reflection_log_3835_neg
  have he : Real.log (11777 / 10000) = -Real.log (10000 / 11777) := by
    rw [show ((11777 / 10000) : ℝ) = ((10000 / 11777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3836_neg : (195649987 / 1000000000) ≤ -Real.log (8223 / 10000) ∧
    -Real.log (8223 / 10000) ≤ (48912497 / 250000000) := by
  have h := checkLog_sound (w := (1777 / 18223)) (n := 12)
    (lo := (195649987 / 1000000000)) (hi := (48912497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8223) = 1/(8223 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3836 : Bounds (-48912497 / 250000000) (-195649987 / 1000000000) (Real.log (8223 / 10000)) := by
  have h := reflection_log_3836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3837_neg : (44421 / 250000000) ≤ -Real.log (10000000 / 10001777) ∧
    -Real.log (10000000 / 10001777) ≤ (35537 / 200000000) := by
  have h := checkLog_sound (w := (1777 / 20001777)) (n := 12)
    (lo := (44421 / 250000000)) (hi := (35537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001777 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001777 / 10000000) = 1/(10000000 / 10001777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3837 : Bounds (44421 / 250000000) (35537 / 200000000) (Real.log (10001777 / 10000000)) := by
  have h := reflection_log_3837_neg
  have he : Real.log (10001777 / 10000000) = -Real.log (10000000 / 10001777) := by
    rw [show ((10001777 / 10000000) : ℝ) = ((10000000 / 10001777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3838_neg : (35543 / 200000000) ≤ -Real.log (9998223 / 10000000) ∧
    -Real.log (9998223 / 10000000) ≤ (44429 / 250000000) := by
  have h := checkLog_sound (w := (1777 / 19998223)) (n := 12)
    (lo := (35543 / 200000000)) (hi := (44429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998223) = 1/(9998223 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3838 : Bounds (-44429 / 250000000) (-35543 / 200000000) (Real.log (9998223 / 10000000)) := by
  have h := reflection_log_3838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3839_neg : (85462761 / 1000000000) ≤ -Real.log (1000000 / 1089221) ∧
    -Real.log (1000000 / 1089221) ≤ (42731381 / 500000000) := by
  have h := checkLog_sound (w := (89221 / 2089221)) (n := 12)
    (lo := (85462761 / 1000000000)) (hi := (42731381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089221 / 1000000) = 1/(1000000 / 1089221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3839 : Bounds (85462761 / 1000000000) (42731381 / 500000000) (Real.log (1089221 / 1000000)) := by
  have h := reflection_log_3839_neg
  have he : Real.log (1089221 / 1000000) = -Real.log (1000000 / 1089221) := by
    rw [show ((1089221 / 1000000) : ℝ) = ((1000000 / 1089221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


