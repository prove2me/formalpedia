-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0031Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0031Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:57:00.036469+00:00
-- url     : https://prove2.me/theorems/b06da188-b5c3-4295-a787-db8d5966ef25
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0031Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0033Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0031Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0032Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0033Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0034Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0035Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0031Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0031
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

theorem reflection_log_1_neg : (340422629 / 500000000) ≤ -Real.log (12800 / 25287) ∧
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


theorem reflection_log_1 : Bounds (340422629 / 500000000) (680845259 / 1000000000) (Real.log (25287 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25287 / 12800) = -Real.log (12800 / 25287) := by
    rw [show ((25287 / 12800) : ℝ) = ((12800 / 25287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (463874657 / 125000000) ≤ -Real.log (313 / 12800) ∧
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


theorem reflection_log_2 : Bounds (-1855498631 / 500000000) (-463874657 / 125000000) (Real.log (313 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170187833 / 250000000) ≤ -Real.log (102400 / 202277) ∧
    -Real.log (102400 / 202277) ≤ (680751333 / 1000000000) := by
  have h := checkLog_sound (w := (99877 / 304677)) (n := 12)
    (lo := (170187833 / 250000000)) (hi := (680751333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202277 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202277 / 102400) = 1/(102400 / 202277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170187833 / 250000000) (680751333 / 1000000000) (Real.log (202277 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202277 / 102400) = -Real.log (102400 / 202277) := by
    rw [show ((202277 / 102400) : ℝ) = ((102400 / 202277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92585951 / 25000000) ≤ -Real.log (2523 / 102400) ∧
    -Real.log (2523 / 102400) ≤ (1851719023 / 500000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2523) = 1/(2523 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1851719023 / 500000000) (-92585951 / 25000000) (Real.log (2523 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20887191 / 31250000) ≤ -Real.log (6400 / 12487) ∧
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


theorem reflection_log_5 : Bounds (20887191 / 31250000) (668390113 / 1000000000) (Real.log (12487 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12487 / 6400) = -Real.log (6400 / 12487) := by
    rw [show ((12487 / 6400) : ℝ) = ((6400 / 12487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (754462519 / 250000000) ≤ -Real.log (313 / 6400) ∧
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


theorem reflection_log_6 : Bounds (-3017850081 / 1000000000) (-754462519 / 250000000) (Real.log (313 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83524987 / 125000000) ≤ -Real.log (51200 / 99877) ∧
    -Real.log (51200 / 99877) ≤ (668199897 / 1000000000) := by
  have h := checkLog_sound (w := (48677 / 151077)) (n := 12)
    (lo := (83524987 / 125000000)) (hi := (668199897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99877 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99877 / 51200) = 1/(51200 / 99877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83524987 / 125000000) (668199897 / 1000000000) (Real.log (99877 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99877 / 51200) = -Real.log (51200 / 99877) := by
    rw [show ((99877 / 51200) : ℝ) = ((51200 / 99877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (150514543 / 50000000) ≤ -Real.log (2523 / 51200) ∧
    -Real.log (2523 / 51200) ≤ (602058173 / 200000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2523) = 1/(2523 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-602058173 / 200000000) (-150514543 / 50000000) (Real.log (2523 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682701817 / 1000000000) ≤ -Real.log (500000 / 989609) ∧
    -Real.log (500000 / 989609) ≤ (341350909 / 500000000) := by
  have h := checkLog_sound (w := (489609 / 1489609)) (n := 12)
    (lo := (682701817 / 1000000000)) (hi := (341350909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989609 / 500000) = 1/(500000 / 989609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682701817 / 1000000000) (341350909 / 500000000) (Real.log (989609 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989609 / 500000) = -Real.log (500000 / 989609) := by
    rw [show ((989609 / 500000) : ℝ) = ((500000 / 989609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (242104253 / 62500000) ≤ -Real.log (10391 / 500000) ∧
    -Real.log (10391 / 500000) ≤ (1936834027 / 500000000) := by
  have h := checkLog_sound (w := (2617 / 13008)) (n := 12)
    (lo := (101983037 / 250000000)) (hi := (407932149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10391) = 1/(10391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1936834027 / 500000000) (-242104253 / 62500000) (Real.log (10391 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682778107 / 1000000000) ≤ -Real.log (1000000 / 1979369) ∧
    -Real.log (1000000 / 1979369) ≤ (170694527 / 250000000) := by
  have h := checkLog_sound (w := (979369 / 2979369)) (n := 12)
    (lo := (682778107 / 1000000000)) (hi := (170694527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979369 / 1000000) = 1/(1000000 / 1979369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682778107 / 1000000000) (170694527 / 250000000) (Real.log (1979369 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979369 / 1000000) = -Real.log (1000000 / 1979369) := by
    rw [show ((1979369 / 1000000) : ℝ) = ((1000000 / 1979369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3880960477 / 1000000000) ≤ -Real.log (20631 / 1000000) ∧
    -Real.log (20631 / 1000000) ≤ (3880960483 / 1000000000) := by
  have h := checkLog_sound (w := (10619 / 51881)) (n := 12)
    (lo := (415224577 / 1000000000)) (hi := (207612289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20631) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20631) = 1/(20631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3880960483 / 1000000000) (-3880960477 / 1000000000) (Real.log (20631 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682652301 / 1000000000) ≤ -Real.log (12500 / 24739) ∧
    -Real.log (12500 / 24739) ≤ (341326151 / 500000000) := by
  have h := checkLog_sound (w := (12239 / 37239)) (n := 12)
    (lo := (682652301 / 1000000000)) (hi := (341326151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24739 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24739 / 12500) = 1/(12500 / 24739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682652301 / 1000000000) (341326151 / 500000000) (Real.log (24739 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24739 / 12500) = -Real.log (12500 / 24739) := by
    rw [show ((24739 / 12500) : ℝ) = ((12500 / 24739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3868963513 / 1000000000) ≤ -Real.log (261 / 12500) ∧
    -Real.log (261 / 12500) ≤ (3868963519 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 5213)) (n := 12)
    (lo := (403227613 / 1000000000)) (hi := (201613807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2088) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2088) = 1/(261 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3868963519 / 1000000000) (-3868963513 / 1000000000) (Real.log (261 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6827291 / 10000000) ≤ -Real.log (125000 / 247409) ∧
    -Real.log (125000 / 247409) ≤ (682729101 / 1000000000) := by
  have h := checkLog_sound (w := (122409 / 372409)) (n := 12)
    (lo := (6827291 / 10000000)) (hi := (682729101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247409 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247409 / 125000) = 1/(125000 / 247409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6827291 / 10000000) (682729101 / 1000000000) (Real.log (247409 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247409 / 125000) = -Real.log (125000 / 247409) := by
    rw [show ((247409 / 125000) : ℝ) = ((125000 / 247409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (484533729 / 125000000) ≤ -Real.log (2591 / 125000) ∧
    -Real.log (2591 / 125000) ≤ (1938134919 / 500000000) := by
  have h := checkLog_sound (w := (5261 / 25989)) (n := 12)
    (lo := (102633483 / 250000000)) (hi := (410533933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10364) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10364) = 1/(2591 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1938134919 / 500000000) (-484533729 / 125000000) (Real.log (2591 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (911273973 / 200000000) ≤ -Real.log (250000000000 / 23809282071023) ∧
    -Real.log (250000000000 / 23809282071023) ≤ (284773117 / 62500000) := by
  have h := checkLog_sound (w := (7809282071023 / 39809282071023)) (n := 12)
    (lo := (79497357 / 200000000)) (hi := (198743393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23809282071023 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23809282071023 / 16000000000000) = 1/(250000000000 / 23809282071023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (911273973 / 200000000) (284773117 / 62500000) (Real.log (23809282071023 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23809282071023 / 250000000000) = -Real.log (250000000000 / 23809282071023) := by
    rw [show ((23809282071023 / 250000000000) : ℝ) = ((250000000000 / 23809282071023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4563738583 / 1000000000) ≤ -Real.log (500000000000 / 47970747903641) ∧
    -Real.log (500000000000 / 47970747903641) ≤ (456373859 / 100000000) := by
  have h := checkLog_sound (w := (15970747903641 / 79970747903641)) (n := 12)
    (lo := (404855503 / 1000000000)) (hi := (25303469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47970747903641 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47970747903641 / 32000000000000) = 1/(500000000000 / 47970747903641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4563738583 / 1000000000) (456373859 / 100000000) (Real.log (47970747903641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (47970747903641 / 500000000000) = -Real.log (500000000000 / 47970747903641) := by
    rw [show ((47970747903641 / 500000000000) : ℝ) = ((500000000000 / 47970747903641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2275807907 / 500000000) ≤ -Real.log (500000000000 / 47392720306513) ∧
    -Real.log (500000000000 / 47392720306513) ≤ (4551615821 / 1000000000) := by
  have h := checkLog_sound (w := (15392720306513 / 79392720306513)) (n := 12)
    (lo := (196366367 / 500000000)) (hi := (78546547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47392720306513 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47392720306513 / 32000000000000) = 1/(500000000000 / 47392720306513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2275807907 / 500000000) (4551615821 / 1000000000) (Real.log (47392720306513 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (47392720306513 / 500000000000) = -Real.log (500000000000 / 47392720306513) := by
    rw [show ((47392720306513 / 500000000000) : ℝ) = ((500000000000 / 47392720306513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1139749733 / 250000000) ≤ -Real.log (500000000000 / 47743921265921) ∧
    -Real.log (500000000000 / 47743921265921) ≤ (4558998939 / 1000000000) := by
  have h := checkLog_sound (w := (15743921265921 / 79743921265921)) (n := 12)
    (lo := (100028963 / 250000000)) (hi := (400115853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47743921265921 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47743921265921 / 32000000000000) = 1/(500000000000 / 47743921265921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1139749733 / 250000000) (4558998939 / 1000000000) (Real.log (47743921265921 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (47743921265921 / 500000000000) = -Real.log (500000000000 / 47743921265921) := by
    rw [show ((47743921265921 / 500000000000) : ℝ) = ((500000000000 / 47743921265921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0031

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032
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

theorem reflection_log_1_neg : (170187833 / 250000000) ≤ -Real.log (102400 / 202277) ∧
    -Real.log (102400 / 202277) ≤ (680751333 / 1000000000) := by
  have h := checkLog_sound (w := (99877 / 304677)) (n := 12)
    (lo := (170187833 / 250000000)) (hi := (680751333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202277 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202277 / 102400) = 1/(102400 / 202277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170187833 / 250000000) (680751333 / 1000000000) (Real.log (202277 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202277 / 102400) = -Real.log (102400 / 202277) := by
    rw [show ((202277 / 102400) : ℝ) = ((102400 / 202277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92585951 / 25000000) ≤ -Real.log (2523 / 102400) ∧
    -Real.log (2523 / 102400) ≤ (1851719023 / 500000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2523) = 1/(2523 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1851719023 / 500000000) (-92585951 / 25000000) (Real.log (2523 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680657397 / 1000000000) ≤ -Real.log (51200 / 101129) ∧
    -Real.log (51200 / 101129) ≤ (340328699 / 500000000) := by
  have h := checkLog_sound (w := (49929 / 152329)) (n := 12)
    (lo := (680657397 / 1000000000)) (hi := (340328699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101129 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101129 / 51200) = 1/(51200 / 101129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680657397 / 1000000000) (340328699 / 500000000) (Real.log (101129 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101129 / 51200) = -Real.log (51200 / 101129) := by
    rw [show ((101129 / 51200) : ℝ) = ((51200 / 101129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3695935537 / 1000000000) ≤ -Real.log (1271 / 51200) ∧
    -Real.log (1271 / 51200) ≤ (3695935543 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1271) = 1/(1271 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3695935543 / 1000000000) (-3695935537 / 1000000000) (Real.log (1271 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83524987 / 125000000) ≤ -Real.log (51200 / 99877) ∧
    -Real.log (51200 / 99877) ≤ (668199897 / 1000000000) := by
  have h := checkLog_sound (w := (48677 / 151077)) (n := 12)
    (lo := (83524987 / 125000000)) (hi := (668199897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99877 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99877 / 51200) = 1/(51200 / 99877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83524987 / 125000000) (668199897 / 1000000000) (Real.log (99877 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99877 / 51200) = -Real.log (51200 / 99877) := by
    rw [show ((99877 / 51200) : ℝ) = ((51200 / 99877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150514543 / 50000000) ≤ -Real.log (2523 / 51200) ∧
    -Real.log (2523 / 51200) ≤ (602058173 / 200000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2523) = 1/(2523 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-602058173 / 200000000) (-150514543 / 50000000) (Real.log (2523 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167002411 / 250000000) ≤ -Real.log (25600 / 49929) ∧
    -Real.log (25600 / 49929) ≤ (133601929 / 200000000) := by
  have h := checkLog_sound (w := (24329 / 75529)) (n := 12)
    (lo := (167002411 / 250000000)) (hi := (133601929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49929 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49929 / 25600) = 1/(25600 / 49929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167002411 / 250000000) (133601929 / 200000000) (Real.log (49929 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49929 / 25600) = -Real.log (25600 / 49929) := by
    rw [show ((49929 / 25600) : ℝ) = ((25600 / 49929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3002788357 / 1000000000) ≤ -Real.log (1271 / 25600) ∧
    -Real.log (1271 / 25600) ≤ (1501394181 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1271) = 1/(1271 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1501394181 / 500000000) (-3002788357 / 1000000000) (Real.log (1271 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341313013 / 500000000) ≤ -Real.log (250000 / 494767) ∧
    -Real.log (250000 / 494767) ≤ (682626027 / 1000000000) := by
  have h := checkLog_sound (w := (244767 / 744767)) (n := 12)
    (lo := (341313013 / 500000000)) (hi := (682626027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494767 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494767 / 250000) = 1/(250000 / 494767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341313013 / 500000000) (682626027 / 1000000000) (Real.log (494767 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (494767 / 250000) = -Real.log (250000 / 494767) := by
    rw [show ((494767 / 250000) : ℝ) = ((250000 / 494767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3866476187 / 1000000000) ≤ -Real.log (5233 / 250000) ∧
    -Real.log (5233 / 250000) ≤ (3866476193 / 1000000000) := by
  have h := checkLog_sound (w := (5159 / 26091)) (n := 12)
    (lo := (400740287 / 1000000000)) (hi := (6261567 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10466) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10466) = 1/(5233 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3866476193 / 1000000000) (-3866476187 / 1000000000) (Real.log (5233 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341351161 / 500000000) ≤ -Real.log (1000000 / 1979219) ∧
    -Real.log (1000000 / 1979219) ≤ (682702323 / 1000000000) := by
  have h := checkLog_sound (w := (979219 / 2979219)) (n := 12)
    (lo := (341351161 / 500000000)) (hi := (682702323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979219 / 1000000) = 1/(1000000 / 1979219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341351161 / 500000000) (682702323 / 1000000000) (Real.log (1979219 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979219 / 1000000) = -Real.log (1000000 / 1979219) := by
    rw [show ((1979219 / 1000000) : ℝ) = ((1000000 / 1979219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (484214521 / 125000000) ≤ -Real.log (20781 / 1000000) ∧
    -Real.log (20781 / 1000000) ≤ (1936858087 / 500000000) := by
  have h := checkLog_sound (w := (10469 / 52031)) (n := 12)
    (lo := (101995067 / 250000000)) (hi := (407980269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20781) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20781) = 1/(20781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1936858087 / 500000000) (-484214521 / 125000000) (Real.log (20781 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85321937 / 125000000) ≤ -Real.log (125000 / 247371) ∧
    -Real.log (125000 / 247371) ≤ (682575497 / 1000000000) := by
  have h := checkLog_sound (w := (122371 / 372371)) (n := 12)
    (lo := (85321937 / 125000000)) (hi := (682575497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247371 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247371 / 125000) = 1/(125000 / 247371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85321937 / 125000000) (682575497 / 1000000000) (Real.log (247371 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247371 / 125000) = -Real.log (125000 / 247371) := by
    rw [show ((247371 / 125000) : ℝ) = ((125000 / 247371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (965427547 / 250000000) ≤ -Real.log (2629 / 125000) ∧
    -Real.log (2629 / 125000) ≤ (1930855097 / 500000000) := by
  have h := checkLog_sound (w := (5109 / 26141)) (n := 12)
    (lo := (24748393 / 62500000)) (hi := (395974289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10516) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10516) = 1/(2629 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1930855097 / 500000000) (-965427547 / 250000000) (Real.log (2629 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341326403 / 500000000) ≤ -Real.log (1000000 / 1979121) ∧
    -Real.log (1000000 / 1979121) ≤ (682652807 / 1000000000) := by
  have h := checkLog_sound (w := (979121 / 2979121)) (n := 12)
    (lo := (341326403 / 500000000)) (hi := (682652807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979121 / 1000000) = 1/(1000000 / 1979121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341326403 / 500000000) (682652807 / 1000000000) (Real.log (1979121 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979121 / 1000000) = -Real.log (1000000 / 1979121) := by
    rw [show ((1979121 / 1000000) : ℝ) = ((1000000 / 1979121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3869011407 / 1000000000) ≤ -Real.log (20879 / 1000000) ∧
    -Real.log (20879 / 1000000) ≤ (3869011413 / 1000000000) := by
  have h := checkLog_sound (w := (10371 / 52129)) (n := 12)
    (lo := (403275507 / 1000000000)) (hi := (100818877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20879) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20879) = 1/(20879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3869011413 / 1000000000) (-3869011407 / 1000000000) (Real.log (20879 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4549102213 / 1000000000) ≤ -Real.log (31250000000 / 2954608971909) ∧
    -Real.log (31250000000 / 2954608971909) ≤ (227455111 / 50000000) := by
  have h := checkLog_sound (w := (954608971909 / 4954608971909)) (n := 12)
    (lo := (390219133 / 1000000000)) (hi := (195109567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2954608971909 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2954608971909 / 2000000000000) = 1/(31250000000 / 2954608971909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4549102213 / 1000000000) (227455111 / 50000000) (Real.log (2954608971909 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2954608971909 / 31250000000) = -Real.log (31250000000 / 2954608971909) := by
    rw [show ((2954608971909 / 31250000000) : ℝ) = ((31250000000 / 2954608971909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (455641849 / 100000000) ≤ -Real.log (6250000000 / 595260995621) ∧
    -Real.log (6250000000 / 595260995621) ≤ (4556418497 / 1000000000) := by
  have h := checkLog_sound (w := (195260995621 / 995260995621)) (n := 12)
    (lo := (39753541 / 100000000)) (hi := (397535411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595260995621 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(595260995621 / 400000000000) = 1/(6250000000 / 595260995621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (455641849 / 100000000) (4556418497 / 1000000000) (Real.log (595260995621 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (595260995621 / 6250000000) = -Real.log (6250000000 / 595260995621) := by
    rw [show ((595260995621 / 6250000000) : ℝ) = ((6250000000 / 595260995621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1136071421 / 250000000) ≤ -Real.log (400000000 / 37637276531) ∧
    -Real.log (400000000 / 37637276531) ≤ (4544285691 / 1000000000) := by
  have h := checkLog_sound (w := (12037276531 / 63237276531)) (n := 12)
    (lo := (96350651 / 250000000)) (hi := (77080521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37637276531 / 25600000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37637276531 / 25600000000) = 1/(400000000 / 37637276531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1136071421 / 250000000) (4544285691 / 1000000000) (Real.log (37637276531 / 400000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37637276531 / 400000000) = -Real.log (400000000 / 37637276531) := by
    rw [show ((37637276531 / 400000000) : ℝ) = ((400000000 / 37637276531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4551664213 / 1000000000) ≤ -Real.log (50000000000 / 4739501412903) ∧
    -Real.log (50000000000 / 4739501412903) ≤ (227583211 / 50000000) := by
  have h := checkLog_sound (w := (1539501412903 / 7939501412903)) (n := 12)
    (lo := (392781133 / 1000000000)) (hi := (196390567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4739501412903 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4739501412903 / 3200000000000) = 1/(50000000000 / 4739501412903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4551664213 / 1000000000) (227583211 / 50000000) (Real.log (4739501412903 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4739501412903 / 50000000000) = -Real.log (50000000000 / 4739501412903) := by
    rw [show ((4739501412903 / 50000000000) : ℝ) = ((50000000000 / 4739501412903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0033Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033
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

theorem reflection_log_1_neg : (680657397 / 1000000000) ≤ -Real.log (51200 / 101129) ∧
    -Real.log (51200 / 101129) ≤ (340328699 / 500000000) := by
  have h := checkLog_sound (w := (49929 / 152329)) (n := 12)
    (lo := (680657397 / 1000000000)) (hi := (340328699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101129 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101129 / 51200) = 1/(51200 / 101129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680657397 / 1000000000) (340328699 / 500000000) (Real.log (101129 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101129 / 51200) = -Real.log (51200 / 101129) := by
    rw [show ((101129 / 51200) : ℝ) = ((51200 / 101129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3695935537 / 1000000000) ≤ -Real.log (1271 / 51200) ∧
    -Real.log (1271 / 51200) ≤ (3695935543 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1271) = 1/(1271 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3695935543 / 1000000000) (-3695935537 / 1000000000) (Real.log (1271 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680563453 / 1000000000) ≤ -Real.log (102400 / 202239) ∧
    -Real.log (102400 / 202239) ≤ (340281727 / 500000000) := by
  have h := checkLog_sound (w := (99839 / 304639)) (n := 12)
    (lo := (680563453 / 1000000000)) (hi := (340281727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202239 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202239 / 102400) = 1/(102400 / 202239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680563453 / 1000000000) (340281727 / 500000000) (Real.log (202239 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202239 / 102400) = -Real.log (102400 / 202239) := by
    rw [show ((202239 / 102400) : ℝ) = ((102400 / 202239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1844244451 / 500000000) ≤ -Real.log (2561 / 102400) ∧
    -Real.log (2561 / 102400) ≤ (922122227 / 250000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2561) = 1/(2561 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-922122227 / 250000000) (-1844244451 / 500000000) (Real.log (2561 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167002411 / 250000000) ≤ -Real.log (25600 / 49929) ∧
    -Real.log (25600 / 49929) ≤ (133601929 / 200000000) := by
  have h := checkLog_sound (w := (24329 / 75529)) (n := 12)
    (lo := (167002411 / 250000000)) (hi := (133601929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49929 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49929 / 25600) = 1/(25600 / 49929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167002411 / 250000000) (133601929 / 200000000) (Real.log (49929 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49929 / 25600) = -Real.log (25600 / 49929) := by
    rw [show ((49929 / 25600) : ℝ) = ((25600 / 49929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3002788357 / 1000000000) ≤ -Real.log (1271 / 25600) ∧
    -Real.log (1271 / 25600) ≤ (1501394181 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1271) = 1/(1271 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1501394181 / 500000000) (-3002788357 / 1000000000) (Real.log (1271 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166954839 / 250000000) ≤ -Real.log (51200 / 99839) ∧
    -Real.log (51200 / 99839) ≤ (667819357 / 1000000000) := by
  have h := checkLog_sound (w := (48639 / 151039)) (n := 12)
    (lo := (166954839 / 250000000)) (hi := (667819357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99839 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99839 / 51200) = 1/(51200 / 99839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166954839 / 250000000) (667819357 / 1000000000) (Real.log (99839 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99839 / 51200) = -Real.log (51200 / 99839) := by
    rw [show ((99839 / 51200) : ℝ) = ((51200 / 99839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1497670861 / 500000000) ≤ -Real.log (2561 / 51200) ∧
    -Real.log (2561 / 51200) ≤ (2995341727 / 1000000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2561) = 1/(2561 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2995341727 / 1000000000) (-1497670861 / 500000000) (Real.log (2561 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68255023 / 100000000) ≤ -Real.log (500000 / 989459) ∧
    -Real.log (500000 / 989459) ≤ (682550231 / 1000000000) := by
  have h := checkLog_sound (w := (489459 / 1489459)) (n := 12)
    (lo := (68255023 / 100000000)) (hi := (682550231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989459 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989459 / 500000) = 1/(500000 / 989459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68255023 / 100000000) (682550231 / 1000000000) (Real.log (989459 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989459 / 500000) = -Real.log (500000 / 989459) := by
    rw [show ((989459 / 500000) : ℝ) = ((500000 / 989459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1507553 / 390625) ≤ -Real.log (10541 / 500000) ∧
    -Real.log (10541 / 500000) ≤ (1929667843 / 500000000) := by
  have h := checkLog_sound (w := (2542 / 13083)) (n := 12)
    (lo := (19679989 / 50000000)) (hi := (393599781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10541) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10541) = 1/(10541 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1929667843 / 500000000) (-1507553 / 390625) (Real.log (10541 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170656633 / 250000000) ≤ -Real.log (1000000 / 1979069) ∧
    -Real.log (1000000 / 1979069) ≤ (682626533 / 1000000000) := by
  have h := checkLog_sound (w := (979069 / 2979069)) (n := 12)
    (lo := (170656633 / 250000000)) (hi := (682626533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979069 / 1000000) = 1/(1000000 / 1979069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170656633 / 250000000) (682626533 / 1000000000) (Real.log (1979069 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979069 / 1000000) = -Real.log (1000000 / 1979069) := by
    rw [show ((1979069 / 1000000) : ℝ) = ((1000000 / 1979069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1933261981 / 500000000) ≤ -Real.log (20931 / 1000000) ∧
    -Real.log (20931 / 1000000) ≤ (60414437 / 15625000) := by
  have h := checkLog_sound (w := (10319 / 52181)) (n := 12)
    (lo := (200394031 / 500000000)) (hi := (400788063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20931) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20931) = 1/(20931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-60414437 / 15625000) (-1933261981 / 500000000) (Real.log (20931 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682499191 / 1000000000) ≤ -Real.log (1000000 / 1978817) ∧
    -Real.log (1000000 / 1978817) ≤ (85312399 / 125000000) := by
  have h := checkLog_sound (w := (978817 / 2978817)) (n := 12)
    (lo := (682499191 / 1000000000)) (hi := (85312399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978817 / 1000000) = 1/(1000000 / 1978817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682499191 / 1000000000) (85312399 / 125000000) (Real.log (1978817 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978817 / 1000000) = -Real.log (1000000 / 1978817) := by
    rw [show ((1978817 / 1000000) : ℝ) = ((1000000 / 1978817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1927278151 / 500000000) ≤ -Real.log (21183 / 1000000) ∧
    -Real.log (21183 / 1000000) ≤ (963639077 / 250000000) := by
  have h := checkLog_sound (w := (10067 / 52433)) (n := 12)
    (lo := (194410201 / 500000000)) (hi := (388820403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21183) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21183) = 1/(21183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-963639077 / 250000000) (-1927278151 / 500000000) (Real.log (21183 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341288001 / 500000000) ≤ -Real.log (1000000 / 1978969) ∧
    -Real.log (1000000 / 1978969) ≤ (682576003 / 1000000000) := by
  have h := checkLog_sound (w := (978969 / 2978969)) (n := 12)
    (lo := (341288001 / 500000000)) (hi := (682576003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978969 / 1000000) = 1/(1000000 / 1978969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341288001 / 500000000) (682576003 / 1000000000) (Real.log (1978969 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978969 / 1000000) = -Real.log (1000000 / 1978969) := by
    rw [show ((1978969 / 1000000) : ℝ) = ((1000000 / 1978969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (482719717 / 125000000) ≤ -Real.log (21031 / 1000000) ∧
    -Real.log (21031 / 1000000) ≤ (1930878871 / 500000000) := by
  have h := checkLog_sound (w := (10219 / 52281)) (n := 12)
    (lo := (99005459 / 250000000)) (hi := (396021837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21031) = 1/(21031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1930878871 / 500000000) (-482719717 / 125000000) (Real.log (21031 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (454188591 / 100000000) ≤ -Real.log (250000000000 / 23466914903709) ∧
    -Real.log (250000000000 / 23466914903709) ≤ (4541885917 / 1000000000) := by
  have h := checkLog_sound (w := (7466914903709 / 39466914903709)) (n := 12)
    (lo := (38300283 / 100000000)) (hi := (383002831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23466914903709 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23466914903709 / 16000000000000) = 1/(250000000000 / 23466914903709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (454188591 / 100000000) (4541885917 / 1000000000) (Real.log (23466914903709 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23466914903709 / 250000000000) = -Real.log (250000000000 / 23466914903709) := by
    rw [show ((23466914903709 / 250000000000) : ℝ) = ((250000000000 / 23466914903709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2274575247 / 500000000) ≤ -Real.log (500000000000 / 47276025990159) ∧
    -Real.log (500000000000 / 47276025990159) ≤ (4549150501 / 1000000000) := by
  have h := checkLog_sound (w := (15276025990159 / 79276025990159)) (n := 12)
    (lo := (195133707 / 500000000)) (hi := (78053483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47276025990159 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47276025990159 / 32000000000000) = 1/(500000000000 / 47276025990159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2274575247 / 500000000) (4549150501 / 1000000000) (Real.log (47276025990159 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (47276025990159 / 500000000000) = -Real.log (500000000000 / 47276025990159) := by
    rw [show ((47276025990159 / 500000000000) : ℝ) = ((500000000000 / 47276025990159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4537055493 / 1000000000) ≤ -Real.log (500000000000 / 46707666525043) ∧
    -Real.log (500000000000 / 46707666525043) ≤ (9074111 / 2000000) := by
  have h := checkLog_sound (w := (14707666525043 / 78707666525043)) (n := 12)
    (lo := (378172413 / 1000000000)) (hi := (189086207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46707666525043 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46707666525043 / 32000000000000) = 1/(500000000000 / 46707666525043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4537055493 / 1000000000) (9074111 / 2000000) (Real.log (46707666525043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (46707666525043 / 500000000000) = -Real.log (500000000000 / 46707666525043) := by
    rw [show ((46707666525043 / 500000000000) : ℝ) = ((500000000000 / 46707666525043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4544333737 / 1000000000) ≤ -Real.log (500000000000 / 47048856450003) ∧
    -Real.log (500000000000 / 47048856450003) ≤ (284020859 / 62500000) := by
  have h := checkLog_sound (w := (15048856450003 / 79048856450003)) (n := 12)
    (lo := (385450657 / 1000000000)) (hi := (192725329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47048856450003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47048856450003 / 32000000000000) = 1/(500000000000 / 47048856450003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4544333737 / 1000000000) (284020859 / 62500000) (Real.log (47048856450003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (47048856450003 / 500000000000) = -Real.log (500000000000 / 47048856450003) := by
    rw [show ((47048856450003 / 500000000000) : ℝ) = ((500000000000 / 47048856450003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034
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

theorem reflection_log_1_neg : (680563453 / 1000000000) ≤ -Real.log (102400 / 202239) ∧
    -Real.log (102400 / 202239) ≤ (340281727 / 500000000) := by
  have h := checkLog_sound (w := (99839 / 304639)) (n := 12)
    (lo := (680563453 / 1000000000)) (hi := (340281727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202239 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202239 / 102400) = 1/(102400 / 202239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680563453 / 1000000000) (340281727 / 500000000) (Real.log (202239 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202239 / 102400) = -Real.log (102400 / 202239) := by
    rw [show ((202239 / 102400) : ℝ) = ((102400 / 202239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1844244451 / 500000000) ≤ -Real.log (2561 / 102400) ∧
    -Real.log (2561 / 102400) ≤ (922122227 / 250000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2561) = 1/(2561 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-922122227 / 250000000) (-1844244451 / 500000000) (Real.log (2561 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680469501 / 1000000000) ≤ -Real.log (5120 / 10111) ∧
    -Real.log (5120 / 10111) ≤ (340234751 / 500000000) := by
  have h := checkLog_sound (w := (4991 / 15231)) (n := 12)
    (lo := (680469501 / 1000000000)) (hi := (340234751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10111 / 5120) = 1/(5120 / 10111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680469501 / 1000000000) (340234751 / 500000000) (Real.log (10111 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (10111 / 5120) = -Real.log (5120 / 10111) := by
    rw [show ((10111 / 5120) : ℝ) = ((5120 / 10111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (368109731 / 100000000) ≤ -Real.log (129 / 5120) ∧
    -Real.log (129 / 5120) ≤ (920274329 / 250000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(160 / 129) = 1/(129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) (Real.log (129 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166954839 / 250000000) ≤ -Real.log (51200 / 99839) ∧
    -Real.log (51200 / 99839) ≤ (667819357 / 1000000000) := by
  have h := checkLog_sound (w := (48639 / 151039)) (n := 12)
    (lo := (166954839 / 250000000)) (hi := (667819357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99839 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99839 / 51200) = 1/(51200 / 99839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166954839 / 250000000) (667819357 / 1000000000) (Real.log (99839 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99839 / 51200) = -Real.log (51200 / 99839) := by
    rw [show ((99839 / 51200) : ℝ) = ((51200 / 99839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1497670861 / 500000000) ≤ -Real.log (2561 / 51200) ∧
    -Real.log (2561 / 51200) ≤ (2995341727 / 1000000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2561) = 1/(2561 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2995341727 / 1000000000) (-1497670861 / 500000000) (Real.log (2561 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667629031 / 1000000000) ≤ -Real.log (2560 / 4991) ∧
    -Real.log (2560 / 4991) ≤ (83453629 / 125000000) := by
  have h := checkLog_sound (w := (2431 / 7551)) (n := 12)
    (lo := (667629031 / 1000000000)) (hi := (83453629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4991 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4991 / 2560) = 1/(2560 / 4991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667629031 / 1000000000) (83453629 / 125000000) (Real.log (4991 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4991 / 2560) = -Real.log (2560 / 4991) := by
    rw [show ((4991 / 2560) : ℝ) = ((2560 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298795013 / 100000000) ≤ -Real.log (129 / 2560) ∧
    -Real.log (129 / 2560) ≤ (597590027 / 200000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 129) = 1/(129 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) (Real.log (129 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341237467 / 500000000) ≤ -Real.log (1000000 / 1978769) ∧
    -Real.log (1000000 / 1978769) ≤ (136494987 / 200000000) := by
  have h := checkLog_sound (w := (978769 / 2978769)) (n := 12)
    (lo := (341237467 / 500000000)) (hi := (136494987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978769 / 1000000) = 1/(1000000 / 1978769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341237467 / 500000000) (136494987 / 200000000) (Real.log (1978769 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978769 / 1000000) = -Real.log (1000000 / 1978769) := by
    rw [show ((1978769 / 1000000) : ℝ) = ((1000000 / 1978769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1926146449 / 500000000) ≤ -Real.log (21231 / 1000000) ∧
    -Real.log (21231 / 1000000) ≤ (481536613 / 125000000) := by
  have h := checkLog_sound (w := (10019 / 52481)) (n := 12)
    (lo := (193278499 / 500000000)) (hi := (386556999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21231) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21231) = 1/(21231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-481536613 / 125000000) (-1926146449 / 500000000) (Real.log (21231 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42659421 / 62500000) ≤ -Real.log (1000000 / 1978919) ∧
    -Real.log (1000000 / 1978919) ≤ (682550737 / 1000000000) := by
  have h := checkLog_sound (w := (978919 / 2978919)) (n := 12)
    (lo := (42659421 / 62500000)) (hi := (682550737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978919 / 1000000) = 1/(1000000 / 1978919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42659421 / 62500000) (682550737 / 1000000000) (Real.log (1978919 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978919 / 1000000) = -Real.log (1000000 / 1978919) := by
    rw [show ((1978919 / 1000000) : ℝ) = ((1000000 / 1978919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (771876623 / 200000000) ≤ -Real.log (21081 / 1000000) ∧
    -Real.log (21081 / 1000000) ≤ (3859383121 / 1000000000) := by
  have h := checkLog_sound (w := (10169 / 52331)) (n := 12)
    (lo := (78729443 / 200000000)) (hi := (24602951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21081) = 1/(21081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3859383121 / 1000000000) (-771876623 / 200000000) (Real.log (21081 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4265143 / 6250000) ≤ -Real.log (500000 / 989333) ∧
    -Real.log (500000 / 989333) ≤ (682422881 / 1000000000) := by
  have h := checkLog_sound (w := (489333 / 1489333)) (n := 12)
    (lo := (4265143 / 6250000)) (hi := (682422881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989333 / 500000) = 1/(500000 / 989333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4265143 / 6250000) (682422881 / 1000000000) (Real.log (989333 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989333 / 500000) = -Real.log (500000 / 989333) := by
    rw [show ((989333 / 500000) : ℝ) = ((500000 / 989333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3847453231 / 1000000000) ≤ -Real.log (10667 / 500000) ∧
    -Real.log (10667 / 500000) ≤ (3847453237 / 1000000000) := by
  have h := checkLog_sound (w := (2479 / 13146)) (n := 12)
    (lo := (381717331 / 1000000000)) (hi := (95429333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10667) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10667) = 1/(10667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3847453237 / 1000000000) (-3847453231 / 1000000000) (Real.log (10667 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42656231 / 62500000) ≤ -Real.log (500000 / 989409) ∧
    -Real.log (500000 / 989409) ≤ (682499697 / 1000000000) := by
  have h := checkLog_sound (w := (489409 / 1489409)) (n := 12)
    (lo := (42656231 / 62500000)) (hi := (682499697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989409 / 500000) = 1/(500000 / 989409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42656231 / 62500000) (682499697 / 1000000000) (Real.log (989409 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (989409 / 500000) = -Real.log (500000 / 989409) := by
    rw [show ((989409 / 500000) : ℝ) = ((500000 / 989409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3854603511 / 1000000000) ≤ -Real.log (10591 / 500000) ∧
    -Real.log (10591 / 500000) ≤ (3854603517 / 1000000000) := by
  have h := checkLog_sound (w := (2517 / 13108)) (n := 12)
    (lo := (388867611 / 1000000000)) (hi := (97216903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10591) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10591) = 1/(10591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3854603517 / 1000000000) (-3854603511 / 1000000000) (Real.log (10591 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (566845979 / 125000000) ≤ -Real.log (125000000000 / 11650234327163) ∧
    -Real.log (125000000000 / 11650234327163) ≤ (4534767839 / 1000000000) := by
  have h := checkLog_sound (w := (3650234327163 / 19650234327163)) (n := 12)
    (lo := (23492797 / 62500000)) (hi := (375884753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11650234327163 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11650234327163 / 8000000000000) = 1/(125000000000 / 11650234327163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (566845979 / 125000000) (4534767839 / 1000000000) (Real.log (11650234327163 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11650234327163 / 125000000000) = -Real.log (125000000000 / 11650234327163) := by
    rw [show ((11650234327163 / 125000000000) : ℝ) = ((125000000000 / 11650234327163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (90838677 / 20000000) ≤ -Real.log (500000000000 / 46936079882359) ∧
    -Real.log (500000000000 / 46936079882359) ≤ (4541933857 / 1000000000) := by
  have h := checkLog_sound (w := (14936079882359 / 78936079882359)) (n := 12)
    (lo := (38305077 / 100000000)) (hi := (383050771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46936079882359 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46936079882359 / 32000000000000) = 1/(500000000000 / 46936079882359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (90838677 / 20000000) (4541933857 / 1000000000) (Real.log (46936079882359 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (46936079882359 / 500000000000) = -Real.log (500000000000 / 46936079882359) := by
    rw [show ((46936079882359 / 500000000000) : ℝ) = ((500000000000 / 46936079882359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4529876111 / 1000000000) ≤ -Real.log (62500000000 / 5796691900253) ∧
    -Real.log (62500000000 / 5796691900253) ≤ (2264938059 / 500000000) := by
  have h := checkLog_sound (w := (1796691900253 / 9796691900253)) (n := 12)
    (lo := (370993031 / 1000000000)) (hi := (46374129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5796691900253 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5796691900253 / 4000000000000) = 1/(62500000000 / 5796691900253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4529876111 / 1000000000) (2264938059 / 500000000) (Real.log (5796691900253 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5796691900253 / 62500000000) = -Real.log (62500000000 / 5796691900253) := by
    rw [show ((5796691900253 / 62500000000) : ℝ) = ((62500000000 / 5796691900253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4537103207 / 1000000000) ≤ -Real.log (500000000000 / 46709895194033) ∧
    -Real.log (500000000000 / 46709895194033) ≤ (2268551607 / 500000000) := by
  have h := checkLog_sound (w := (14709895194033 / 78709895194033)) (n := 12)
    (lo := (378220127 / 1000000000)) (hi := (11819379 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46709895194033 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46709895194033 / 32000000000000) = 1/(500000000000 / 46709895194033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4537103207 / 1000000000) (2268551607 / 500000000) (Real.log (46709895194033 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (46709895194033 / 500000000000) = -Real.log (500000000000 / 46709895194033) := by
    rw [show ((46709895194033 / 500000000000) : ℝ) = ((500000000000 / 46709895194033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035
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

theorem reflection_log_1_neg : (680469501 / 1000000000) ≤ -Real.log (5120 / 10111) ∧
    -Real.log (5120 / 10111) ≤ (340234751 / 500000000) := by
  have h := checkLog_sound (w := (4991 / 15231)) (n := 12)
    (lo := (680469501 / 1000000000)) (hi := (340234751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10111 / 5120) = 1/(5120 / 10111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680469501 / 1000000000) (340234751 / 500000000) (Real.log (10111 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (10111 / 5120) = -Real.log (5120 / 10111) := by
    rw [show ((10111 / 5120) : ℝ) = ((5120 / 10111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (368109731 / 100000000) ≤ -Real.log (129 / 5120) ∧
    -Real.log (129 / 5120) ≤ (920274329 / 250000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(160 / 129) = 1/(129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) (Real.log (129 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680375539 / 1000000000) ≤ -Real.log (102400 / 202201) ∧
    -Real.log (102400 / 202201) ≤ (34018777 / 50000000) := by
  have h := checkLog_sound (w := (99801 / 304601)) (n := 12)
    (lo := (680375539 / 1000000000)) (hi := (34018777 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202201 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202201 / 102400) = 1/(102400 / 202201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680375539 / 1000000000) (34018777 / 50000000) (Real.log (202201 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202201 / 102400) = -Real.log (102400 / 202201) := by
    rw [show ((202201 / 102400) : ℝ) = ((102400 / 202201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1836879977 / 500000000) ≤ -Real.log (2599 / 102400) ∧
    -Real.log (2599 / 102400) ≤ (91843999 / 25000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2599) = 1/(2599 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) (Real.log (2599 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667629031 / 1000000000) ≤ -Real.log (2560 / 4991) ∧
    -Real.log (2560 / 4991) ≤ (83453629 / 125000000) := by
  have h := checkLog_sound (w := (2431 / 7551)) (n := 12)
    (lo := (667629031 / 1000000000)) (hi := (83453629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4991 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4991 / 2560) = 1/(2560 / 4991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667629031 / 1000000000) (83453629 / 125000000) (Real.log (4991 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4991 / 2560) = -Real.log (2560 / 4991) := by
    rw [show ((4991 / 2560) : ℝ) = ((2560 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298795013 / 100000000) ≤ -Real.log (129 / 2560) ∧
    -Real.log (129 / 2560) ≤ (597590027 / 200000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 129) = 1/(129 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) (Real.log (129 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667438671 / 1000000000) ≤ -Real.log (51200 / 99801) ∧
    -Real.log (51200 / 99801) ≤ (41714917 / 62500000) := by
  have h := checkLog_sound (w := (48601 / 151001)) (n := 12)
    (lo := (667438671 / 1000000000)) (hi := (41714917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99801 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99801 / 51200) = 1/(51200 / 99801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667438671 / 1000000000) (41714917 / 62500000) (Real.log (99801 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99801 / 51200) = -Real.log (51200 / 99801) := by
    rw [show ((99801 / 51200) : ℝ) = ((51200 / 99801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1490306387 / 500000000) ≤ -Real.log (2599 / 51200) ∧
    -Real.log (2599 / 51200) ≤ (2980612779 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2599) = 1/(2599 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) (Real.log (2599 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341199563 / 500000000) ≤ -Real.log (1000000 / 1978619) ∧
    -Real.log (1000000 / 1978619) ≤ (682399127 / 1000000000) := by
  have h := checkLog_sound (w := (978619 / 2978619)) (n := 12)
    (lo := (341199563 / 500000000)) (hi := (682399127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978619 / 1000000) = 1/(1000000 / 1978619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341199563 / 500000000) (682399127 / 1000000000) (Real.log (1978619 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978619 / 1000000) = -Real.log (1000000 / 1978619) := by
    rw [show ((1978619 / 1000000) : ℝ) = ((1000000 / 1978619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1922626299 / 500000000) ≤ -Real.log (21381 / 1000000) ∧
    -Real.log (21381 / 1000000) ≤ (961313151 / 250000000) := by
  have h := checkLog_sound (w := (9869 / 52631)) (n := 12)
    (lo := (189758349 / 500000000)) (hi := (379516699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21381) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21381) = 1/(21381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-961313151 / 250000000) (-1922626299 / 500000000) (Real.log (21381 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682475439 / 1000000000) ≤ -Real.log (100000 / 197877) ∧
    -Real.log (100000 / 197877) ≤ (8530943 / 12500000) := by
  have h := checkLog_sound (w := (97877 / 297877)) (n := 12)
    (lo := (682475439 / 1000000000)) (hi := (8530943 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197877 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197877 / 100000) = 1/(100000 / 197877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682475439 / 1000000000) (8530943 / 12500000) (Real.log (197877 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (197877 / 100000) = -Real.log (100000 / 197877) := by
    rw [show ((197877 / 100000) : ℝ) = ((100000 / 197877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192617 / 50000) ≤ -Real.log (2123 / 100000) ∧
    -Real.log (2123 / 100000) ≤ (1926170003 / 500000000) := by
  have h := checkLog_sound (w := (501 / 2624)) (n := 12)
    (lo := (3866041 / 10000000)) (hi := (386604101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2123) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2123) = 1/(2123 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1926170003 / 500000000) (-192617 / 50000) (Real.log (2123 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682346563 / 1000000000) ≤ -Real.log (200000 / 395703) ∧
    -Real.log (200000 / 395703) ≤ (170586641 / 250000000) := by
  have h := checkLog_sound (w := (195703 / 595703)) (n := 12)
    (lo := (682346563 / 1000000000)) (hi := (170586641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395703 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395703 / 200000) = 1/(200000 / 395703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682346563 / 1000000000) (170586641 / 250000000) (Real.log (395703 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395703 / 200000) = -Real.log (200000 / 395703) := by
    rw [show ((395703 / 200000) : ℝ) = ((200000 / 395703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1920200129 / 500000000) ≤ -Real.log (4297 / 200000) ∧
    -Real.log (4297 / 200000) ≤ (480050033 / 125000000) := by
  have h := checkLog_sound (w := (1953 / 10547)) (n := 12)
    (lo := (187332179 / 500000000)) (hi := (374664359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4297) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4297) = 1/(4297 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-480050033 / 125000000) (-1920200129 / 500000000) (Real.log (4297 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136484677 / 200000000) ≤ -Real.log (1000000 / 1978667) ∧
    -Real.log (1000000 / 1978667) ≤ (341211693 / 500000000) := by
  have h := checkLog_sound (w := (978667 / 2978667)) (n := 12)
    (lo := (136484677 / 200000000)) (hi := (341211693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978667 / 1000000) = 1/(1000000 / 1978667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136484677 / 200000000) (341211693 / 500000000) (Real.log (1978667 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978667 / 1000000) = -Real.log (1000000 / 1978667) := by
    rw [show ((1978667 / 1000000) : ℝ) = ((1000000 / 1978667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1923750053 / 500000000) ≤ -Real.log (21333 / 1000000) ∧
    -Real.log (21333 / 1000000) ≤ (240468757 / 62500000) := by
  have h := checkLog_sound (w := (9917 / 52583)) (n := 12)
    (lo := (190882103 / 500000000)) (hi := (381764207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21333) = 1/(21333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-240468757 / 62500000) (-1923750053 / 500000000) (Real.log (21333 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (181106069 / 40000000) ≤ -Real.log (31250000000 / 2891906073149) ∧
    -Real.log (31250000000 / 2891906073149) ≤ (1131912933 / 250000000) := by
  have h := checkLog_sound (w := (891906073149 / 4891906073149)) (n := 12)
    (lo := (73753729 / 200000000)) (hi := (184384323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2891906073149 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2891906073149 / 2000000000000) = 1/(31250000000 / 2891906073149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181106069 / 40000000) (1131912933 / 250000000) (Real.log (2891906073149 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2891906073149 / 31250000000) = -Real.log (31250000000 / 2891906073149) := by
    rw [show ((2891906073149 / 31250000000) : ℝ) = ((31250000000 / 2891906073149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4534815439 / 1000000000) ≤ -Real.log (500000000000 / 46603155911447) ∧
    -Real.log (500000000000 / 46603155911447) ≤ (2267407723 / 500000000) := by
  have h := checkLog_sound (w := (14603155911447 / 78603155911447)) (n := 12)
    (lo := (375932359 / 1000000000)) (hi := (9398309 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46603155911447 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46603155911447 / 32000000000000) = 1/(500000000000 / 46603155911447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4534815439 / 1000000000) (2267407723 / 500000000) (Real.log (46603155911447 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (46603155911447 / 500000000000) = -Real.log (500000000000 / 46603155911447) := by
    rw [show ((46603155911447 / 500000000000) : ℝ) = ((500000000000 / 46603155911447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4522746821 / 1000000000) ≤ -Real.log (500000000000 / 46044100535257) ∧
    -Real.log (500000000000 / 46044100535257) ≤ (1130686707 / 250000000) := by
  have h := checkLog_sound (w := (14044100535257 / 78044100535257)) (n := 12)
    (lo := (363863741 / 1000000000)) (hi := (181931871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46044100535257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46044100535257 / 32000000000000) = 1/(500000000000 / 46044100535257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4522746821 / 1000000000) (1130686707 / 250000000) (Real.log (46044100535257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (46044100535257 / 500000000000) = -Real.log (500000000000 / 46044100535257) := by
    rw [show ((46044100535257 / 500000000000) : ℝ) = ((500000000000 / 46044100535257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4529923491 / 1000000000) ≤ -Real.log (12500000000 / 1159393310833) ∧
    -Real.log (12500000000 / 1159393310833) ≤ (2264961749 / 500000000) := by
  have h := checkLog_sound (w := (359393310833 / 1959393310833)) (n := 12)
    (lo := (371040411 / 1000000000)) (hi := (92760103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159393310833 / 800000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1159393310833 / 800000000000) = 1/(12500000000 / 1159393310833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4529923491 / 1000000000) (2264961749 / 500000000) (Real.log (1159393310833 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1159393310833 / 12500000000) = -Real.log (12500000000 / 1159393310833) := by
    rw [show ((1159393310833 / 12500000000) : ℝ) = ((12500000000 / 1159393310833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035

end


