-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0026Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0026Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:55:28.243985+00:00
-- url     : https://prove2.me/theorems/b275ea6f-bd76-489a-9f96-ad217ac3898c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0026Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0027Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0026Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0030Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0026Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0030Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0026Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0030Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0026Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0027Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0028Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0029Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0030Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0026Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0026
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (681314757 / 1000000000) ≤ -Real.log (102400 / 202391) ∧
    -Real.log (102400 / 202391) ≤ (340657379 / 500000000) := by
  have h := checkLog_sound (w := (99991 / 304791)) (n := 12)
    (lo := (681314757 / 1000000000)) (hi := (340657379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202391 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202391 / 102400) = 1/(102400 / 202391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (681314757 / 1000000000) (340657379 / 500000000) (Real.log (202391 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202391 / 102400) = -Real.log (102400 / 202391) := by
    rw [show ((202391 / 102400) : ℝ) = ((102400 / 202391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1874837493 / 500000000) ≤ -Real.log (2409 / 102400) ∧
    -Real.log (2409 / 102400) ≤ (234354687 / 62500000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2409) = 1/(2409 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-234354687 / 62500000) (-1874837493 / 500000000) (Real.log (2409 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5449767 / 8000000) ≤ -Real.log (25600 / 50593) ∧
    -Real.log (25600 / 50593) ≤ (170305219 / 250000000) := by
  have h := checkLog_sound (w := (24993 / 76193)) (n := 12)
    (lo := (5449767 / 8000000)) (hi := (170305219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50593 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50593 / 25600) = 1/(25600 / 50593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5449767 / 8000000) (170305219 / 250000000) (Real.log (50593 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50593 / 25600) = -Real.log (25600 / 50593) := by
    rw [show ((50593 / 25600) : ℝ) = ((25600 / 50593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (935454709 / 250000000) ≤ -Real.log (607 / 25600) ∧
    -Real.log (607 / 25600) ≤ (1870909421 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 607) = 1/(607 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1870909421 / 500000000) (-935454709 / 250000000) (Real.log (607 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669340649 / 1000000000) ≤ -Real.log (51200 / 99991) ∧
    -Real.log (51200 / 99991) ≤ (13386813 / 20000000) := by
  have h := checkLog_sound (w := (48791 / 151191)) (n := 12)
    (lo := (669340649 / 1000000000)) (hi := (13386813 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99991 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99991 / 51200) = 1/(51200 / 99991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (669340649 / 1000000000) (13386813 / 20000000) (Real.log (99991 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99991 / 51200) = -Real.log (51200 / 99991) := by
    rw [show ((99991 / 51200) : ℝ) = ((51200 / 99991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1528263903 / 500000000) ≤ -Real.log (2409 / 51200) ∧
    -Real.log (2409 / 51200) ≤ (3056527811 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2409) = 1/(2409 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3056527811 / 1000000000) (-1528263903 / 500000000) (Real.log (2409 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (334575307 / 500000000) ≤ -Real.log (12800 / 24993) ∧
    -Real.log (12800 / 24993) ≤ (133830123 / 200000000) := by
  have h := checkLog_sound (w := (12193 / 37793)) (n := 12)
    (lo := (334575307 / 500000000)) (hi := (133830123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24993 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24993 / 12800) = 1/(12800 / 24993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (334575307 / 500000000) (133830123 / 200000000) (Real.log (24993 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24993 / 12800) = -Real.log (12800 / 24993) := by
    rw [show ((24993 / 12800) : ℝ) = ((12800 / 24993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (381083957 / 125000000) ≤ -Real.log (607 / 12800) ∧
    -Real.log (607 / 12800) ≤ (3048671661 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 607) = 1/(607 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3048671661 / 1000000000) (-381083957 / 125000000) (Real.log (607 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341540341 / 500000000) ≤ -Real.log (15625 / 30937) ∧
    -Real.log (15625 / 30937) ≤ (683080683 / 1000000000) := by
  have h := checkLog_sound (w := (7656 / 23281)) (n := 12)
    (lo := (341540341 / 500000000)) (hi := (683080683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30937 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30937 / 15625) = 1/(15625 / 30937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341540341 / 500000000) (683080683 / 1000000000) (Real.log (30937 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (30937 / 15625) = -Real.log (15625 / 30937) := by
    rw [show ((30937 / 15625) : ℝ) = ((15625 / 30937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3910424281 / 1000000000) ≤ -Real.log (313 / 15625) ∧
    -Real.log (313 / 15625) ≤ (3910424287 / 1000000000) := by
  have h := checkLog_sound (w := (5609 / 25641)) (n := 12)
    (lo := (444688381 / 1000000000)) (hi := (222344191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10016) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10016) = 1/(313 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3910424287 / 1000000000) (-3910424281 / 1000000000) (Real.log (313 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683156943 / 1000000000) ≤ -Real.log (1000000 / 1980119) ∧
    -Real.log (1000000 / 1980119) ≤ (42697309 / 62500000) := by
  have h := checkLog_sound (w := (980119 / 2980119)) (n := 12)
    (lo := (683156943 / 1000000000)) (hi := (42697309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980119 / 1000000) = 1/(1000000 / 1980119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683156943 / 1000000000) (42697309 / 62500000) (Real.log (1980119 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980119 / 1000000) = -Real.log (1000000 / 1980119) := by
    rw [show ((1980119 / 1000000) : ℝ) = ((1000000 / 1980119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1958995387 / 500000000) ≤ -Real.log (19881 / 1000000) ∧
    -Real.log (19881 / 1000000) ≤ (195899539 / 50000000) := by
  have h := checkLog_sound (w := (11369 / 51131)) (n := 12)
    (lo := (226127437 / 500000000)) (hi := (3618039 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19881) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19881) = 1/(19881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195899539 / 50000000) (-1958995387 / 500000000) (Real.log (19881 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341517613 / 500000000) ≤ -Real.log (500000 / 989939) ∧
    -Real.log (500000 / 989939) ≤ (683035227 / 1000000000) := by
  have h := checkLog_sound (w := (489939 / 1489939)) (n := 12)
    (lo := (341517613 / 500000000)) (hi := (683035227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989939 / 500000) = 1/(500000 / 989939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341517613 / 500000000) (683035227 / 1000000000) (Real.log (989939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989939 / 500000) = -Real.log (500000 / 989939) := by
    rw [show ((989939 / 500000) : ℝ) = ((500000 / 989939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (976485383 / 250000000) ≤ -Real.log (10061 / 500000) ∧
    -Real.log (10061 / 500000) ≤ (1952970769 / 500000000) := by
  have h := checkLog_sound (w := (2782 / 12843)) (n := 12)
    (lo := (6878213 / 15625000)) (hi := (440205633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10061) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10061) = 1/(10061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1952970769 / 500000000) (-976485383 / 250000000) (Real.log (10061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683112501 / 1000000000) ≤ -Real.log (1000000 / 1980031) ∧
    -Real.log (1000000 / 1980031) ≤ (341556251 / 500000000) := by
  have h := checkLog_sound (w := (980031 / 2980031)) (n := 12)
    (lo := (683112501 / 1000000000)) (hi := (341556251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980031 / 1000000) = 1/(1000000 / 1980031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683112501 / 1000000000) (341556251 / 500000000) (Real.log (1980031 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1980031 / 1000000) = -Real.log (1000000 / 1980031) := by
    rw [show ((1980031 / 1000000) : ℝ) = ((1000000 / 1980031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (782714841 / 200000000) ≤ -Real.log (19969 / 1000000) ∧
    -Real.log (19969 / 1000000) ≤ (3913574211 / 1000000000) := by
  have h := checkLog_sound (w := (11281 / 51219)) (n := 12)
    (lo := (89567661 / 200000000)) (hi := (223919153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19969) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19969) = 1/(19969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3913574211 / 1000000000) (-782714841 / 200000000) (Real.log (19969 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4593504963 / 1000000000) ≤ -Real.log (500000000000 / 49420127795527) ∧
    -Real.log (500000000000 / 49420127795527) ≤ (459350497 / 100000000) := by
  have h := checkLog_sound (w := (17420127795527 / 81420127795527)) (n := 12)
    (lo := (434621883 / 1000000000)) (hi := (108655471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49420127795527 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49420127795527 / 32000000000000) = 1/(500000000000 / 49420127795527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4593504963 / 1000000000) (459350497 / 100000000) (Real.log (49420127795527 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (49420127795527 / 500000000000) = -Real.log (500000000000 / 49420127795527) := by
    rw [show ((49420127795527 / 500000000000) : ℝ) = ((500000000000 / 49420127795527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4601147717 / 1000000000) ≤ -Real.log (250000000000 / 24899640360143) ∧
    -Real.log (250000000000 / 24899640360143) ≤ (1150286931 / 250000000) := by
  have h := checkLog_sound (w := (8899640360143 / 40899640360143)) (n := 12)
    (lo := (442264637 / 1000000000)) (hi := (221132319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24899640360143 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24899640360143 / 16000000000000) = 1/(250000000000 / 24899640360143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4601147717 / 1000000000) (1150286931 / 250000000) (Real.log (24899640360143 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24899640360143 / 250000000000) = -Real.log (250000000000 / 24899640360143) := by
    rw [show ((24899640360143 / 250000000000) : ℝ) = ((250000000000 / 24899640360143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2294488379 / 500000000) ≤ -Real.log (500000000000 / 49196849219759) ∧
    -Real.log (500000000000 / 49196849219759) ≤ (917795353 / 200000000) := by
  have h := checkLog_sound (w := (17196849219759 / 81196849219759)) (n := 12)
    (lo := (215046839 / 500000000)) (hi := (430093679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49196849219759 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49196849219759 / 32000000000000) = 1/(500000000000 / 49196849219759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2294488379 / 500000000) (917795353 / 200000000) (Real.log (49196849219759 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49196849219759 / 500000000000) = -Real.log (500000000000 / 49196849219759) := by
    rw [show ((49196849219759 / 500000000000) : ℝ) = ((500000000000 / 49196849219759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (919337341 / 200000000) ≤ -Real.log (500000000000 / 49577620311483) ∧
    -Real.log (500000000000 / 49577620311483) ≤ (574585839 / 125000000) := by
  have h := checkLog_sound (w := (17577620311483 / 81577620311483)) (n := 12)
    (lo := (3502429 / 8000000)) (hi := (218901813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49577620311483 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49577620311483 / 32000000000000) = 1/(500000000000 / 49577620311483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (919337341 / 200000000) (574585839 / 125000000) (Real.log (49577620311483 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49577620311483 / 500000000000) = -Real.log (500000000000 / 49577620311483) := by
    rw [show ((49577620311483 / 500000000000) : ℝ) = ((500000000000 / 49577620311483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0026

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0027Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0027
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (5449767 / 8000000) ≤ -Real.log (25600 / 50593) ∧
    -Real.log (25600 / 50593) ≤ (170305219 / 250000000) := by
  have h := checkLog_sound (w := (24993 / 76193)) (n := 12)
    (lo := (5449767 / 8000000)) (hi := (170305219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50593 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50593 / 25600) = 1/(25600 / 50593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5449767 / 8000000) (170305219 / 250000000) (Real.log (50593 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50593 / 25600) = -Real.log (25600 / 50593) := by
    rw [show ((50593 / 25600) : ℝ) = ((25600 / 50593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (935454709 / 250000000) ≤ -Real.log (607 / 25600) ∧
    -Real.log (607 / 25600) ≤ (1870909421 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 607) = 1/(607 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1870909421 / 500000000) (-935454709 / 250000000) (Real.log (607 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85140873 / 125000000) ≤ -Real.log (102400 / 202353) ∧
    -Real.log (102400 / 202353) ≤ (136225397 / 200000000) := by
  have h := checkLog_sound (w := (99953 / 304753)) (n := 12)
    (lo := (85140873 / 125000000)) (hi := (136225397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202353 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202353 / 102400) = 1/(102400 / 202353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (85140873 / 125000000) (136225397 / 200000000) (Real.log (202353 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202353 / 102400) = -Real.log (102400 / 202353) := by
    rw [show ((202353 / 102400) : ℝ) = ((102400 / 202353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149360957 / 40000000) ≤ -Real.log (2447 / 102400) ∧
    -Real.log (2447 / 102400) ≤ (3734023931 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2447) = 1/(2447 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3734023931 / 1000000000) (-149360957 / 40000000) (Real.log (2447 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (334575307 / 500000000) ≤ -Real.log (12800 / 24993) ∧
    -Real.log (12800 / 24993) ≤ (133830123 / 200000000) := by
  have h := checkLog_sound (w := (12193 / 37793)) (n := 12)
    (lo := (334575307 / 500000000)) (hi := (133830123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24993 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24993 / 12800) = 1/(12800 / 24993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (334575307 / 500000000) (133830123 / 200000000) (Real.log (24993 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24993 / 12800) = -Real.log (12800 / 24993) := by
    rw [show ((24993 / 12800) : ℝ) = ((12800 / 24993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (381083957 / 125000000) ≤ -Real.log (607 / 12800) ∧
    -Real.log (607 / 12800) ≤ (3048671661 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 607) = 1/(607 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3048671661 / 1000000000) (-381083957 / 125000000) (Real.log (607 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (668960543 / 1000000000) ≤ -Real.log (51200 / 99953) ∧
    -Real.log (51200 / 99953) ≤ (20905017 / 31250000) := by
  have h := checkLog_sound (w := (48753 / 151153)) (n := 12)
    (lo := (668960543 / 1000000000)) (hi := (20905017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99953 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99953 / 51200) = 1/(51200 / 99953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (668960543 / 1000000000) (20905017 / 31250000) (Real.log (99953 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99953 / 51200) = -Real.log (51200 / 99953) := by
    rw [show ((99953 / 51200) : ℝ) = ((51200 / 99953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (608175349 / 200000000) ≤ -Real.log (2447 / 51200) ∧
    -Real.log (2447 / 51200) ≤ (12163507 / 4000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2447) = 1/(2447 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12163507 / 4000000) (-608175349 / 200000000) (Real.log (2447 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1333993 / 1953125) ≤ -Real.log (1000000 / 1979817) ∧
    -Real.log (1000000 / 1979817) ≤ (683004417 / 1000000000) := by
  have h := checkLog_sound (w := (979817 / 2979817)) (n := 12)
    (lo := (1333993 / 1953125)) (hi := (683004417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979817 / 1000000) = 1/(1000000 / 1979817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1333993 / 1953125) (683004417 / 1000000000) (Real.log (1979817 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979817 / 1000000) = -Real.log (1000000 / 1979817) := by
    rw [show ((1979817 / 1000000) : ℝ) = ((1000000 / 1979817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (390291461 / 100000000) ≤ -Real.log (20183 / 1000000) ∧
    -Real.log (20183 / 1000000) ≤ (487864327 / 125000000) := by
  have h := checkLog_sound (w := (11067 / 51433)) (n := 12)
    (lo := (43717871 / 100000000)) (hi := (437178711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20183) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20183) = 1/(20183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487864327 / 125000000) (-390291461 / 100000000) (Real.log (20183 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170770297 / 250000000) ≤ -Real.log (1000000 / 1979969) ∧
    -Real.log (1000000 / 1979969) ≤ (683081189 / 1000000000) := by
  have h := checkLog_sound (w := (979969 / 2979969)) (n := 12)
    (lo := (170770297 / 250000000)) (hi := (683081189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979969 / 1000000) = 1/(1000000 / 1979969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170770297 / 250000000) (683081189 / 1000000000) (Real.log (1979969 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979969 / 1000000) = -Real.log (1000000 / 1979969) := by
    rw [show ((1979969 / 1000000) : ℝ) = ((1000000 / 1979969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1955237101 / 500000000) ≤ -Real.log (20031 / 1000000) ∧
    -Real.log (20031 / 1000000) ≤ (122202319 / 31250000) := by
  have h := checkLog_sound (w := (11219 / 51281)) (n := 12)
    (lo := (222369151 / 500000000)) (hi := (444738303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20031) = 1/(20031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-122202319 / 31250000) (-1955237101 / 500000000) (Real.log (20031 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682958451 / 1000000000) ≤ -Real.log (500000 / 989863) ∧
    -Real.log (500000 / 989863) ≤ (170739613 / 250000000) := by
  have h := checkLog_sound (w := (489863 / 1489863)) (n := 12)
    (lo := (682958451 / 1000000000)) (hi := (170739613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989863 / 500000) = 1/(500000 / 989863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682958451 / 1000000000) (170739613 / 250000000) (Real.log (989863 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989863 / 500000) = -Real.log (500000 / 989863) := by
    rw [show ((989863 / 500000) : ℝ) = ((500000 / 989863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3898415999 / 1000000000) ≤ -Real.log (10137 / 500000) ∧
    -Real.log (10137 / 500000) ≤ (779683201 / 200000000) := by
  have h := checkLog_sound (w := (2744 / 12881)) (n := 12)
    (lo := (432680099 / 1000000000)) (hi := (4326801 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10137) = 1/(10137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-779683201 / 200000000) (-3898415999 / 1000000000) (Real.log (10137 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683035731 / 1000000000) ≤ -Real.log (1000000 / 1979879) ∧
    -Real.log (1000000 / 1979879) ≤ (170758933 / 250000000) := by
  have h := checkLog_sound (w := (979879 / 2979879)) (n := 12)
    (lo := (683035731 / 1000000000)) (hi := (170758933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979879 / 1000000) = 1/(1000000 / 1979879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683035731 / 1000000000) (170758933 / 250000000) (Real.log (1979879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979879 / 1000000) = -Real.log (1000000 / 1979879) := by
    rw [show ((1979879 / 1000000) : ℝ) = ((1000000 / 1979879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (390599123 / 100000000) ≤ -Real.log (20121 / 1000000) ∧
    -Real.log (20121 / 1000000) ≤ (976497809 / 250000000) := by
  have h := checkLog_sound (w := (11129 / 51371)) (n := 12)
    (lo := (44025533 / 100000000)) (hi := (440255331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20121) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20121) = 1/(20121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-976497809 / 250000000) (-390599123 / 100000000) (Real.log (20121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (183436761 / 40000000) ≤ -Real.log (500000000000 / 49046648169251) ∧
    -Real.log (500000000000 / 49046648169251) ≤ (573239879 / 125000000) := by
  have h := checkLog_sound (w := (17046648169251 / 81046648169251)) (n := 12)
    (lo := (85407189 / 200000000)) (hi := (213517973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49046648169251 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49046648169251 / 32000000000000) = 1/(500000000000 / 49046648169251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (183436761 / 40000000) (573239879 / 125000000) (Real.log (49046648169251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (49046648169251 / 500000000000) = -Real.log (500000000000 / 49046648169251) := by
    rw [show ((49046648169251 / 500000000000) : ℝ) = ((500000000000 / 49046648169251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (459355539 / 100000000) ≤ -Real.log (100000000000 / 9884523987819) ∧
    -Real.log (100000000000 / 9884523987819) ≤ (4593555397 / 1000000000) := by
  have h := checkLog_sound (w := (3484523987819 / 16284523987819)) (n := 12)
    (lo := (43467231 / 100000000)) (hi := (434672311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9884523987819 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9884523987819 / 6400000000000) = 1/(100000000000 / 9884523987819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (459355539 / 100000000) (4593555397 / 1000000000) (Real.log (9884523987819 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9884523987819 / 100000000000) = -Real.log (100000000000 / 9884523987819) := by
    rw [show ((9884523987819 / 100000000000) : ℝ) = ((100000000000 / 9884523987819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4581374449 / 1000000000) ≤ -Real.log (250000000000 / 24412128834961) ∧
    -Real.log (250000000000 / 24412128834961) ≤ (572671807 / 125000000) := by
  have h := checkLog_sound (w := (8412128834961 / 40412128834961)) (n := 12)
    (lo := (422491369 / 1000000000)) (hi := (42249137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24412128834961 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24412128834961 / 16000000000000) = 1/(250000000000 / 24412128834961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4581374449 / 1000000000) (572671807 / 125000000) (Real.log (24412128834961 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24412128834961 / 250000000000) = -Real.log (250000000000 / 24412128834961) := by
    rw [show ((24412128834961 / 250000000000) : ℝ) = ((250000000000 / 24412128834961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4589026961 / 1000000000) ≤ -Real.log (500000000000 / 49199319119329) ∧
    -Real.log (500000000000 / 49199319119329) ≤ (573628371 / 125000000) := by
  have h := checkLog_sound (w := (17199319119329 / 81199319119329)) (n := 12)
    (lo := (430143881 / 1000000000)) (hi := (215071941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49199319119329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49199319119329 / 32000000000000) = 1/(500000000000 / 49199319119329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4589026961 / 1000000000) (573628371 / 125000000) (Real.log (49199319119329 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49199319119329 / 500000000000) = -Real.log (500000000000 / 49199319119329) := by
    rw [show ((49199319119329 / 500000000000) : ℝ) = ((500000000000 / 49199319119329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0027

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0028Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0028
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (85140873 / 125000000) ≤ -Real.log (102400 / 202353) ∧
    -Real.log (102400 / 202353) ≤ (136225397 / 200000000) := by
  have h := checkLog_sound (w := (99953 / 304753)) (n := 12)
    (lo := (85140873 / 125000000)) (hi := (136225397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202353 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202353 / 102400) = 1/(102400 / 202353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85140873 / 125000000) (136225397 / 200000000) (Real.log (202353 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202353 / 102400) = -Real.log (102400 / 202353) := by
    rw [show ((202353 / 102400) : ℝ) = ((102400 / 202353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149360957 / 40000000) ≤ -Real.log (2447 / 102400) ∧
    -Real.log (2447 / 102400) ≤ (3734023931 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2447) = 1/(2447 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3734023931 / 1000000000) (-149360957 / 40000000) (Real.log (2447 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170258271 / 250000000) ≤ -Real.log (51200 / 101167) ∧
    -Real.log (51200 / 101167) ≤ (136206617 / 200000000) := by
  have h := checkLog_sound (w := (49967 / 152367)) (n := 12)
    (lo := (170258271 / 250000000)) (hi := (136206617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101167 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101167 / 51200) = 1/(51200 / 101167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170258271 / 250000000) (136206617 / 200000000) (Real.log (101167 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101167 / 51200) = -Real.log (51200 / 101167) := by
    rw [show ((101167 / 51200) : ℝ) = ((51200 / 101167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (745257861 / 200000000) ≤ -Real.log (1233 / 51200) ∧
    -Real.log (1233 / 51200) ≤ (3726289311 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1233) = 1/(1233 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3726289311 / 1000000000) (-745257861 / 200000000) (Real.log (1233 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (668960543 / 1000000000) ≤ -Real.log (51200 / 99953) ∧
    -Real.log (51200 / 99953) ≤ (20905017 / 31250000) := by
  have h := checkLog_sound (w := (48753 / 151153)) (n := 12)
    (lo := (668960543 / 1000000000)) (hi := (20905017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99953 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99953 / 51200) = 1/(51200 / 99953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (668960543 / 1000000000) (20905017 / 31250000) (Real.log (99953 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99953 / 51200) = -Real.log (51200 / 99953) := by
    rw [show ((99953 / 51200) : ℝ) = ((51200 / 99953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (608175349 / 200000000) ≤ -Real.log (2447 / 51200) ∧
    -Real.log (2447 / 51200) ≤ (12163507 / 4000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2447) = 1/(2447 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12163507 / 4000000) (-608175349 / 200000000) (Real.log (2447 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167192609 / 250000000) ≤ -Real.log (25600 / 49967) ∧
    -Real.log (25600 / 49967) ≤ (668770437 / 1000000000) := by
  have h := checkLog_sound (w := (24367 / 75567)) (n := 12)
    (lo := (167192609 / 250000000)) (hi := (668770437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49967 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49967 / 25600) = 1/(25600 / 49967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167192609 / 250000000) (668770437 / 1000000000) (Real.log (49967 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49967 / 25600) = -Real.log (25600 / 49967) := by
    rw [show ((49967 / 25600) : ℝ) = ((25600 / 49967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (24265137 / 8000000) ≤ -Real.log (1233 / 25600) ∧
    -Real.log (1233 / 25600) ≤ (303314213 / 100000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1233) = 1/(1233 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-303314213 / 100000000) (-24265137 / 8000000) (Real.log (1233 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85366081 / 125000000) ≤ -Real.log (1000000 / 1979667) ∧
    -Real.log (1000000 / 1979667) ≤ (682928649 / 1000000000) := by
  have h := checkLog_sound (w := (979667 / 2979667)) (n := 12)
    (lo := (85366081 / 125000000)) (hi := (682928649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979667 / 1000000) = 1/(1000000 / 1979667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85366081 / 125000000) (682928649 / 1000000000) (Real.log (1979667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979667 / 1000000) = -Real.log (1000000 / 1979667) := by
    rw [show ((1979667 / 1000000) : ℝ) = ((1000000 / 1979667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1947755047 / 500000000) ≤ -Real.log (20333 / 1000000) ∧
    -Real.log (20333 / 1000000) ≤ (38955101 / 10000000) := by
  have h := checkLog_sound (w := (10917 / 51583)) (n := 12)
    (lo := (214887097 / 500000000)) (hi := (85954839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20333) = 1/(20333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38955101 / 10000000) (-1947755047 / 500000000) (Real.log (20333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683004921 / 1000000000) ≤ -Real.log (500000 / 989909) ∧
    -Real.log (500000 / 989909) ≤ (341502461 / 500000000) := by
  have h := checkLog_sound (w := (489909 / 1489909)) (n := 12)
    (lo := (683004921 / 1000000000)) (hi := (341502461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989909 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989909 / 500000) = 1/(500000 / 989909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683004921 / 1000000000) (341502461 / 500000000) (Real.log (989909 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (989909 / 500000) = -Real.log (500000 / 989909) := by
    rw [show ((989909 / 500000) : ℝ) = ((500000 / 989909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1951482079 / 500000000) ≤ -Real.log (10091 / 500000) ∧
    -Real.log (10091 / 500000) ≤ (975741041 / 250000000) := by
  have h := checkLog_sound (w := (2767 / 12858)) (n := 12)
    (lo := (218614129 / 500000000)) (hi := (437228259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10091) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10091) = 1/(10091 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-975741041 / 250000000) (-1951482079 / 500000000) (Real.log (10091 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68288167 / 100000000) ≤ -Real.log (500000 / 989787) ∧
    -Real.log (500000 / 989787) ≤ (682881671 / 1000000000) := by
  have h := checkLog_sound (w := (489787 / 1489787)) (n := 12)
    (lo := (68288167 / 100000000)) (hi := (682881671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989787 / 500000) = 1/(500000 / 989787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68288167 / 100000000) (682881671 / 1000000000) (Real.log (989787 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989787 / 500000) = -Real.log (500000 / 989787) := by
    rw [show ((989787 / 500000) : ℝ) = ((500000 / 989787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3890946677 / 1000000000) ≤ -Real.log (10213 / 500000) ∧
    -Real.log (10213 / 500000) ≤ (3890946683 / 1000000000) := by
  have h := checkLog_sound (w := (2706 / 12919)) (n := 12)
    (lo := (425210777 / 1000000000)) (hi := (212605389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10213) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10213) = 1/(10213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3890946683 / 1000000000) (-3890946677 / 1000000000) (Real.log (10213 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170739739 / 250000000) ≤ -Real.log (1000000 / 1979727) ∧
    -Real.log (1000000 / 1979727) ≤ (682958957 / 1000000000) := by
  have h := checkLog_sound (w := (979727 / 2979727)) (n := 12)
    (lo := (170739739 / 250000000)) (hi := (682958957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979727 / 1000000) = 1/(1000000 / 1979727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170739739 / 250000000) (682958957 / 1000000000) (Real.log (1979727 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979727 / 1000000) = -Real.log (1000000 / 1979727) := by
    rw [show ((1979727 / 1000000) : ℝ) = ((1000000 / 1979727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (974616331 / 250000000) ≤ -Real.log (20273 / 1000000) ∧
    -Real.log (20273 / 1000000) ≤ (389846533 / 100000000) := by
  have h := checkLog_sound (w := (10977 / 51523)) (n := 12)
    (lo := (27045589 / 62500000)) (hi := (17309177 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20273) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20273) = 1/(20273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-389846533 / 100000000) (-974616331 / 250000000) (Real.log (20273 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2289219371 / 500000000) ≤ -Real.log (62500000000 / 6085141764619) ∧
    -Real.log (62500000000 / 6085141764619) ≤ (4578438749 / 1000000000) := by
  have h := checkLog_sound (w := (2085141764619 / 10085141764619)) (n := 12)
    (lo := (209777831 / 500000000)) (hi := (419555663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6085141764619 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6085141764619 / 4000000000000) = 1/(62500000000 / 6085141764619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2289219371 / 500000000) (4578438749 / 1000000000) (Real.log (6085141764619 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6085141764619 / 62500000000) = -Real.log (62500000000 / 6085141764619) := by
    rw [show ((6085141764619 / 62500000000) : ℝ) = ((62500000000 / 6085141764619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2292984539 / 500000000) ≤ -Real.log (500000000000 / 49049103161233) ∧
    -Real.log (500000000000 / 49049103161233) ≤ (917193817 / 200000000) := by
  have h := checkLog_sound (w := (17049103161233 / 81049103161233)) (n := 12)
    (lo := (213542999 / 500000000)) (hi := (427085999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49049103161233 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49049103161233 / 32000000000000) = 1/(500000000000 / 49049103161233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2292984539 / 500000000) (917193817 / 200000000) (Real.log (49049103161233 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (49049103161233 / 500000000000) = -Real.log (500000000000 / 49049103161233) := by
    rw [show ((49049103161233 / 500000000000) : ℝ) = ((500000000000 / 49049103161233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2286914173 / 500000000) ≤ -Real.log (250000000000 / 24228605698619) ∧
    -Real.log (250000000000 / 24228605698619) ≤ (4573828353 / 1000000000) := by
  have h := checkLog_sound (w := (8228605698619 / 40228605698619)) (n := 12)
    (lo := (207472633 / 500000000)) (hi := (414945267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24228605698619 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24228605698619 / 16000000000000) = 1/(250000000000 / 24228605698619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2286914173 / 500000000) (4573828353 / 1000000000) (Real.log (24228605698619 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24228605698619 / 250000000000) = -Real.log (250000000000 / 24228605698619) := by
    rw [show ((24228605698619 / 250000000000) : ℝ) = ((250000000000 / 24228605698619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114535607 / 25000000) ≤ -Real.log (500000000000 / 48826690672323) ∧
    -Real.log (500000000000 / 48826690672323) ≤ (4581424287 / 1000000000) := by
  have h := checkLog_sound (w := (16826690672323 / 80826690672323)) (n := 12)
    (lo := (1056353 / 2500000)) (hi := (422541201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48826690672323 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48826690672323 / 32000000000000) = 1/(500000000000 / 48826690672323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114535607 / 25000000) (4581424287 / 1000000000) (Real.log (48826690672323 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48826690672323 / 500000000000) = -Real.log (500000000000 / 48826690672323) := by
    rw [show ((48826690672323 / 500000000000) : ℝ) = ((500000000000 / 48826690672323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0028

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0029Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0029
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (170258271 / 250000000) ≤ -Real.log (51200 / 101167) ∧
    -Real.log (51200 / 101167) ≤ (136206617 / 200000000) := by
  have h := checkLog_sound (w := (49967 / 152367)) (n := 12)
    (lo := (170258271 / 250000000)) (hi := (136206617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101167 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101167 / 51200) = 1/(51200 / 101167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170258271 / 250000000) (136206617 / 200000000) (Real.log (101167 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101167 / 51200) = -Real.log (51200 / 101167) := by
    rw [show ((101167 / 51200) : ℝ) = ((51200 / 101167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (745257861 / 200000000) ≤ -Real.log (1233 / 51200) ∧
    -Real.log (1233 / 51200) ≤ (3726289311 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1233) = 1/(1233 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3726289311 / 1000000000) (-745257861 / 200000000) (Real.log (1233 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85117397 / 125000000) ≤ -Real.log (20480 / 40463) ∧
    -Real.log (20480 / 40463) ≤ (680939177 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 60943)) (n := 12)
    (lo := (85117397 / 125000000)) (hi := (680939177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40463 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40463 / 20480) = 1/(20480 / 40463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (85117397 / 125000000) (680939177 / 1000000000) (Real.log (40463 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40463 / 20480) = -Real.log (20480 / 40463) := by
    rw [show ((40463 / 20480) : ℝ) = ((20480 / 40463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74372281 / 20000000) ≤ -Real.log (497 / 20480) ∧
    -Real.log (497 / 20480) ≤ (464826757 / 125000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 497) = 1/(497 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-464826757 / 125000000) (-74372281 / 20000000) (Real.log (497 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167192609 / 250000000) ≤ -Real.log (25600 / 49967) ∧
    -Real.log (25600 / 49967) ≤ (668770437 / 1000000000) := by
  have h := checkLog_sound (w := (24367 / 75567)) (n := 12)
    (lo := (167192609 / 250000000)) (hi := (668770437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49967 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49967 / 25600) = 1/(25600 / 49967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167192609 / 250000000) (668770437 / 1000000000) (Real.log (49967 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49967 / 25600) = -Real.log (25600 / 49967) := by
    rw [show ((49967 / 25600) : ℝ) = ((25600 / 49967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (24265137 / 8000000) ≤ -Real.log (1233 / 25600) ∧
    -Real.log (1233 / 25600) ≤ (303314213 / 100000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1233) = 1/(1233 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-303314213 / 100000000) (-24265137 / 8000000) (Real.log (1233 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167145073 / 250000000) ≤ -Real.log (10240 / 19983) ∧
    -Real.log (10240 / 19983) ≤ (668580293 / 1000000000) := by
  have h := checkLog_sound (w := (9743 / 30223)) (n := 12)
    (lo := (167145073 / 250000000)) (hi := (668580293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19983 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19983 / 10240) = 1/(10240 / 19983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167145073 / 250000000) (668580293 / 1000000000) (Real.log (19983 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19983 / 10240) = -Real.log (10240 / 19983) := by
    rw [show ((19983 / 10240) : ℝ) = ((10240 / 19983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (302546687 / 100000000) ≤ -Real.log (497 / 10240) ∧
    -Real.log (497 / 10240) ≤ (4840747 / 1600000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 497) = 1/(497 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4840747 / 1600000) (-302546687 / 100000000) (Real.log (497 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5462823 / 8000000) ≤ -Real.log (1000000 / 1979517) ∧
    -Real.log (1000000 / 1979517) ≤ (170713219 / 250000000) := by
  have h := checkLog_sound (w := (979517 / 2979517)) (n := 12)
    (lo := (5462823 / 8000000)) (hi := (170713219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979517 / 1000000) = 1/(1000000 / 1979517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5462823 / 8000000) (170713219 / 250000000) (Real.log (1979517 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979517 / 1000000) = -Real.log (1000000 / 1979517) := by
    rw [show ((1979517 / 1000000) : ℝ) = ((1000000 / 1979517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1944080001 / 500000000) ≤ -Real.log (20483 / 1000000) ∧
    -Real.log (20483 / 1000000) ≤ (486020001 / 125000000) := by
  have h := checkLog_sound (w := (10767 / 51733)) (n := 12)
    (lo := (211212051 / 500000000)) (hi := (422424103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20483) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20483) = 1/(20483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-486020001 / 125000000) (-1944080001 / 500000000) (Real.log (20483 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682929153 / 1000000000) ≤ -Real.log (250000 / 494917) ∧
    -Real.log (250000 / 494917) ≤ (341464577 / 500000000) := by
  have h := checkLog_sound (w := (244917 / 744917)) (n := 12)
    (lo := (682929153 / 1000000000)) (hi := (341464577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494917 / 250000) = 1/(250000 / 494917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682929153 / 1000000000) (341464577 / 500000000) (Real.log (494917 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494917 / 250000) = -Real.log (250000 / 494917) := by
    rw [show ((494917 / 250000) : ℝ) = ((250000 / 494917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (973889819 / 250000000) ≤ -Real.log (5083 / 250000) ∧
    -Real.log (5083 / 250000) ≤ (1947779641 / 500000000) := by
  have h := checkLog_sound (w := (5459 / 25791)) (n := 12)
    (lo := (26863961 / 62500000)) (hi := (429823377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10166) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10166) = 1/(5083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1947779641 / 500000000) (-973889819 / 250000000) (Real.log (5083 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170701347 / 250000000) ≤ -Real.log (1000000 / 1979423) ∧
    -Real.log (1000000 / 1979423) ≤ (682805389 / 1000000000) := by
  have h := checkLog_sound (w := (979423 / 2979423)) (n := 12)
    (lo := (170701347 / 250000000)) (hi := (682805389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979423 / 1000000) = 1/(1000000 / 1979423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170701347 / 250000000) (682805389 / 1000000000) (Real.log (1979423 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1979423 / 1000000) = -Real.log (1000000 / 1979423) := by
    rw [show ((1979423 / 1000000) : ℝ) = ((1000000 / 1979423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242723833 / 62500000) ≤ -Real.log (20577 / 1000000) ∧
    -Real.log (20577 / 1000000) ≤ (1941790667 / 500000000) := by
  have h := checkLog_sound (w := (10673 / 51827)) (n := 12)
    (lo := (104461357 / 250000000)) (hi := (417845429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20577) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20577) = 1/(20577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1941790667 / 500000000) (-242723833 / 62500000) (Real.log (20577 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27315287 / 40000000) ≤ -Real.log (40000 / 79183) ∧
    -Real.log (40000 / 79183) ≤ (5335017 / 7812500) := by
  have h := checkLog_sound (w := (39183 / 119183)) (n := 12)
    (lo := (27315287 / 40000000)) (hi := (5335017 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79183 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79183 / 40000) = 1/(40000 / 79183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27315287 / 40000000) (5335017 / 7812500) (Real.log (79183 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79183 / 40000) = -Real.log (40000 / 79183) := by
    rw [show ((79183 / 40000) : ℝ) = ((40000 / 79183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (778199127 / 200000000) ≤ -Real.log (817 / 40000) ∧
    -Real.log (817 / 40000) ≤ (3890995641 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2067)) (n := 12)
    (lo := (85051947 / 200000000)) (hi := (53157467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 817) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 817) = 1/(817 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3890995641 / 1000000000) (-778199127 / 200000000) (Real.log (817 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4571012877 / 1000000000) ≤ -Real.log (500000000000 / 48320973490211) ∧
    -Real.log (500000000000 / 48320973490211) ≤ (1142753221 / 250000000) := by
  have h := checkLog_sound (w := (16320973490211 / 80320973490211)) (n := 12)
    (lo := (412129797 / 1000000000)) (hi := (206064899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48320973490211 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48320973490211 / 32000000000000) = 1/(500000000000 / 48320973490211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4571012877 / 1000000000) (1142753221 / 250000000) (Real.log (48320973490211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (48320973490211 / 500000000000) = -Real.log (500000000000 / 48320973490211) := by
    rw [show ((48320973490211 / 500000000000) : ℝ) = ((500000000000 / 48320973490211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4578488429 / 1000000000) ≤ -Real.log (500000000000 / 48683553019871) ∧
    -Real.log (500000000000 / 48683553019871) ≤ (1144622109 / 250000000) := by
  have h := checkLog_sound (w := (16683553019871 / 80683553019871)) (n := 12)
    (lo := (419605349 / 1000000000)) (hi := (8392107 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48683553019871 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48683553019871 / 32000000000000) = 1/(500000000000 / 48683553019871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4578488429 / 1000000000) (1144622109 / 250000000) (Real.log (48683553019871 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (48683553019871 / 500000000000) = -Real.log (500000000000 / 48683553019871) := by
    rw [show ((48683553019871 / 500000000000) : ℝ) = ((500000000000 / 48683553019871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1141596679 / 250000000) ≤ -Real.log (100000000000 / 9619589833309) ∧
    -Real.log (100000000000 / 9619589833309) ≤ (4566386723 / 1000000000) := by
  have h := checkLog_sound (w := (3219589833309 / 16019589833309)) (n := 12)
    (lo := (101875909 / 250000000)) (hi := (407503637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9619589833309 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9619589833309 / 6400000000000) = 1/(100000000000 / 9619589833309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1141596679 / 250000000) (4566386723 / 1000000000) (Real.log (9619589833309 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9619589833309 / 100000000000) = -Real.log (100000000000 / 9619589833309) := by
    rw [show ((9619589833309 / 100000000000) : ℝ) = ((100000000000 / 9619589833309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (457387781 / 100000000) ≤ -Real.log (250000000000 / 24229804161567) ∧
    -Real.log (250000000000 / 24229804161567) ≤ (4573877817 / 1000000000) := by
  have h := checkLog_sound (w := (8229804161567 / 40229804161567)) (n := 12)
    (lo := (41499473 / 100000000)) (hi := (414994731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24229804161567 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24229804161567 / 16000000000000) = 1/(250000000000 / 24229804161567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (457387781 / 100000000) (4573877817 / 1000000000) (Real.log (24229804161567 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24229804161567 / 250000000000) = -Real.log (250000000000 / 24229804161567) := by
    rw [show ((24229804161567 / 250000000000) : ℝ) = ((250000000000 / 24229804161567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0029

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0030Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0030
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (85117397 / 125000000) ≤ -Real.log (20480 / 40463) ∧
    -Real.log (20480 / 40463) ≤ (680939177 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 60943)) (n := 12)
    (lo := (85117397 / 125000000)) (hi := (680939177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40463 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40463 / 20480) = 1/(20480 / 40463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85117397 / 125000000) (680939177 / 1000000000) (Real.log (40463 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40463 / 20480) = -Real.log (20480 / 40463) := by
    rw [show ((40463 / 20480) : ℝ) = ((20480 / 40463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74372281 / 20000000) ≤ -Real.log (497 / 20480) ∧
    -Real.log (497 / 20480) ≤ (464826757 / 125000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 497) = 1/(497 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-464826757 / 125000000) (-74372281 / 20000000) (Real.log (497 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (340422629 / 500000000) ≤ -Real.log (12800 / 25287) ∧
    -Real.log (12800 / 25287) ≤ (680845259 / 1000000000) := by
  have h := checkLog_sound (w := (12487 / 38087)) (n := 12)
    (lo := (340422629 / 500000000)) (hi := (680845259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25287 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25287 / 12800) = 1/(12800 / 25287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (340422629 / 500000000) (680845259 / 1000000000) (Real.log (25287 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25287 / 12800) = -Real.log (12800 / 25287) := by
    rw [show ((25287 / 12800) : ℝ) = ((12800 / 25287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (463874657 / 125000000) ≤ -Real.log (313 / 12800) ∧
    -Real.log (313 / 12800) ≤ (1855498631 / 500000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 313) = 1/(313 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1855498631 / 500000000) (-463874657 / 125000000) (Real.log (313 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167145073 / 250000000) ≤ -Real.log (10240 / 19983) ∧
    -Real.log (10240 / 19983) ≤ (668580293 / 1000000000) := by
  have h := checkLog_sound (w := (9743 / 30223)) (n := 12)
    (lo := (167145073 / 250000000)) (hi := (668580293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19983 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19983 / 10240) = 1/(10240 / 19983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167145073 / 250000000) (668580293 / 1000000000) (Real.log (19983 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19983 / 10240) = -Real.log (10240 / 19983) := by
    rw [show ((19983 / 10240) : ℝ) = ((10240 / 19983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302546687 / 100000000) ≤ -Real.log (497 / 10240) ∧
    -Real.log (497 / 10240) ≤ (4840747 / 1600000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 497) = 1/(497 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4840747 / 1600000) (-302546687 / 100000000) (Real.log (497 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20887191 / 31250000) ≤ -Real.log (6400 / 12487) ∧
    -Real.log (6400 / 12487) ≤ (668390113 / 1000000000) := by
  have h := checkLog_sound (w := (6087 / 18887)) (n := 12)
    (lo := (20887191 / 31250000)) (hi := (668390113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12487 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12487 / 6400) = 1/(6400 / 12487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20887191 / 31250000) (668390113 / 1000000000) (Real.log (12487 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12487 / 6400) = -Real.log (6400 / 12487) := by
    rw [show ((12487 / 6400) : ℝ) = ((6400 / 12487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (754462519 / 250000000) ≤ -Real.log (313 / 6400) ∧
    -Real.log (313 / 6400) ≤ (3017850081 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 313) = 1/(313 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3017850081 / 1000000000) (-754462519 / 250000000) (Real.log (313 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682777601 / 1000000000) ≤ -Real.log (125000 / 247421) ∧
    -Real.log (125000 / 247421) ≤ (341388801 / 500000000) := by
  have h := checkLog_sound (w := (122421 / 372421)) (n := 12)
    (lo := (682777601 / 1000000000)) (hi := (341388801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247421 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247421 / 125000) = 1/(125000 / 247421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682777601 / 1000000000) (341388801 / 500000000) (Real.log (247421 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247421 / 125000) = -Real.log (125000 / 247421) := by
    rw [show ((247421 / 125000) : ℝ) = ((125000 / 247421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3880912007 / 1000000000) ≤ -Real.log (2579 / 125000) ∧
    -Real.log (2579 / 125000) ≤ (3880912013 / 1000000000) := by
  have h := checkLog_sound (w := (5309 / 25941)) (n := 12)
    (lo := (415176107 / 1000000000)) (hi := (103794027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10316) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10316) = 1/(2579 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3880912013 / 1000000000) (-3880912007 / 1000000000) (Real.log (2579 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34142669 / 50000000) ≤ -Real.log (500000 / 989759) ∧
    -Real.log (500000 / 989759) ≤ (682853381 / 1000000000) := by
  have h := checkLog_sound (w := (489759 / 1489759)) (n := 12)
    (lo := (34142669 / 50000000)) (hi := (682853381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989759 / 500000) = 1/(500000 / 989759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34142669 / 50000000) (682853381 / 1000000000) (Real.log (989759 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (989759 / 500000) = -Real.log (500000 / 989759) := by
    rw [show ((989759 / 500000) : ℝ) = ((500000 / 989759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (486026103 / 125000000) ≤ -Real.log (10241 / 500000) ∧
    -Real.log (10241 / 500000) ≤ (388820883 / 100000000) := by
  have h := checkLog_sound (w := (2692 / 12933)) (n := 12)
    (lo := (105618231 / 250000000)) (hi := (16898917 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10241) = 1/(10241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-388820883 / 100000000) (-486026103 / 125000000) (Real.log (10241 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136545719 / 200000000) ≤ -Real.log (1000000 / 1979271) ∧
    -Real.log (1000000 / 1979271) ≤ (170682149 / 250000000) := by
  have h := checkLog_sound (w := (979271 / 2979271)) (n := 12)
    (lo := (136545719 / 200000000)) (hi := (170682149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979271 / 1000000) = 1/(1000000 / 1979271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136545719 / 200000000) (170682149 / 250000000) (Real.log (1979271 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1979271 / 1000000) = -Real.log (1000000 / 1979271) := by
    rw [show ((1979271 / 1000000) : ℝ) = ((1000000 / 1979271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (387622159 / 100000000) ≤ -Real.log (20729 / 1000000) ∧
    -Real.log (20729 / 1000000) ≤ (969055399 / 250000000) := by
  have h := checkLog_sound (w := (10521 / 51979)) (n := 12)
    (lo := (41048569 / 100000000)) (hi := (410485691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20729) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20729) = 1/(20729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-969055399 / 250000000) (-387622159 / 100000000) (Real.log (20729 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682805893 / 1000000000) ≤ -Real.log (31250 / 61857) ∧
    -Real.log (31250 / 61857) ≤ (341402947 / 500000000) := by
  have h := checkLog_sound (w := (30607 / 93107)) (n := 12)
    (lo := (682805893 / 1000000000)) (hi := (341402947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61857 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61857 / 31250) = 1/(31250 / 61857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682805893 / 1000000000) (341402947 / 500000000) (Real.log (61857 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (61857 / 31250) = -Real.log (31250 / 61857) := by
    rw [show ((61857 / 31250) : ℝ) = ((31250 / 61857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (485453741 / 125000000) ≤ -Real.log (643 / 31250) ∧
    -Real.log (643 / 31250) ≤ (1941814967 / 500000000) := by
  have h := checkLog_sound (w := (5337 / 25913)) (n := 12)
    (lo := (104473507 / 250000000)) (hi := (417894029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10288) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10288) = 1/(643 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1941814967 / 500000000) (-485453741 / 125000000) (Real.log (643 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (570461201 / 125000000) ≤ -Real.log (50000000000 / 4796839860411) ∧
    -Real.log (50000000000 / 4796839860411) ≤ (912737923 / 200000000) := by
  have h := checkLog_sound (w := (1596839860411 / 7996839860411)) (n := 12)
    (lo := (3162551 / 7812500)) (hi := (404806529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4796839860411 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4796839860411 / 3200000000000) = 1/(50000000000 / 4796839860411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (570461201 / 125000000) (912737923 / 200000000) (Real.log (4796839860411 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4796839860411 / 50000000000) = -Real.log (50000000000 / 4796839860411) := by
    rw [show ((4796839860411 / 50000000000) : ℝ) = ((50000000000 / 4796839860411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1142765551 / 250000000) ≤ -Real.log (250000000000 / 24161678547017) ∧
    -Real.log (250000000000 / 24161678547017) ≤ (4571062211 / 1000000000) := by
  have h := checkLog_sound (w := (8161678547017 / 40161678547017)) (n := 12)
    (lo := (103044781 / 250000000)) (hi := (3297433 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24161678547017 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24161678547017 / 16000000000000) = 1/(250000000000 / 24161678547017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1142765551 / 250000000) (4571062211 / 1000000000) (Real.log (24161678547017 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24161678547017 / 250000000000) = -Real.log (250000000000 / 24161678547017) := by
    rw [show ((24161678547017 / 250000000000) : ℝ) = ((250000000000 / 24161678547017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (569868773 / 125000000) ≤ -Real.log (250000000000 / 23870796951131) ∧
    -Real.log (250000000000 / 23870796951131) ≤ (4558950191 / 1000000000) := by
  have h := checkLog_sound (w := (7870796951131 / 39870796951131)) (n := 12)
    (lo := (12502097 / 31250000)) (hi := (80013421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23870796951131 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23870796951131 / 16000000000000) = 1/(250000000000 / 23870796951131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (569868773 / 125000000) (4558950191 / 1000000000) (Real.log (23870796951131 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (23870796951131 / 250000000000) = -Real.log (250000000000 / 23870796951131) := by
    rw [show ((23870796951131 / 250000000000) : ℝ) = ((250000000000 / 23870796951131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (228321791 / 50000000) ≤ -Real.log (500000000000 / 48100311041991) ∧
    -Real.log (500000000000 / 48100311041991) ≤ (4566435827 / 1000000000) := by
  have h := checkLog_sound (w := (16100311041991 / 80100311041991)) (n := 12)
    (lo := (20377637 / 50000000)) (hi := (407552741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48100311041991 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48100311041991 / 32000000000000) = 1/(500000000000 / 48100311041991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (228321791 / 50000000) (4566435827 / 1000000000) (Real.log (48100311041991 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48100311041991 / 500000000000) = -Real.log (500000000000 / 48100311041991) := by
    rw [show ((48100311041991 / 500000000000) : ℝ) = ((500000000000 / 48100311041991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0030

end


