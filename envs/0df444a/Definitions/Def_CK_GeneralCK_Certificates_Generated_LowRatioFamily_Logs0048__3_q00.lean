-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:09:44.391155+00:00
-- url     : https://prove2.me/theorems/d70c9e08-ebff-45eb-a918-a4001b907059
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0048 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0049, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0050) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3072_neg : (18127443 / 200000000) ≤ -Real.log (913349 / 1000000) ∧
    -Real.log (913349 / 1000000) ≤ (2832413 / 31250000) := by
  have h := checkLog_sound (w := (86651 / 1913349)) (n := 12)
    (lo := (18127443 / 200000000)) (hi := (2832413 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913349) = 1/(913349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3072 : Bounds (-2832413 / 31250000) (-18127443 / 200000000) (Real.log (913349 / 1000000)) := by
  have h := reflection_log_3072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3073_neg : (301469 / 40000000) ≤ -Real.log (992491604199 / 1000000000000) ∧
    -Real.log (992491604199 / 1000000000000) ≤ (3768363 / 500000000) := by
  have h := checkLog_sound (w := (7508395801 / 1992491604199)) (n := 12)
    (lo := (301469 / 40000000)) (hi := (3768363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992491604199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992491604199) = 1/(992491604199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3073 : Bounds (-3768363 / 500000000) (-301469 / 40000000) (Real.log (992491604199 / 1000000000000)) := by
  have h := reflection_log_3073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3074_neg : (7497837 / 1000000000) ≤ -Real.log (62033137551 / 62500000000) ∧
    -Real.log (62033137551 / 62500000000) ≤ (3748919 / 500000000) := by
  have h := checkLog_sound (w := (466862449 / 124533137551)) (n := 12)
    (lo := (7497837 / 1000000000)) (hi := (3748919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62033137551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62033137551) = 1/(62033137551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3074 : Bounds (-3748919 / 500000000) (-7497837 / 1000000000) (Real.log (62033137551 / 62500000000)) := by
  have h := reflection_log_3074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3075_neg : (173288339 / 1000000000) ≤ -Real.log (250000000000 / 297302237809) ∧
    -Real.log (250000000000 / 297302237809) ≤ (8664417 / 50000000) := by
  have h := checkLog_sound (w := (47302237809 / 547302237809)) (n := 12)
    (lo := (173288339 / 1000000000)) (hi := (8664417 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297302237809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297302237809 / 250000000000) = 1/(250000000000 / 297302237809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3075 : Bounds (173288339 / 1000000000) (8664417 / 50000000) (Real.log (297302237809 / 250000000000)) := by
  have h := reflection_log_3075_neg
  have he : Real.log (297302237809 / 250000000000) = -Real.log (250000000000 / 297302237809) := by
    rw [show ((297302237809 / 250000000000) : ℝ) = ((250000000000 / 297302237809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3076_neg : (21717213 / 125000000) ≤ -Real.log (500000000000 / 594871730303) ∧
    -Real.log (500000000000 / 594871730303) ≤ (34747541 / 200000000) := by
  have h := checkLog_sound (w := (94871730303 / 1094871730303)) (n := 12)
    (lo := (21717213 / 125000000)) (hi := (34747541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594871730303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594871730303 / 500000000000) = 1/(500000000000 / 594871730303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3076 : Bounds (21717213 / 125000000) (34747541 / 200000000) (Real.log (594871730303 / 500000000000)) := by
  have h := reflection_log_3076_neg
  have he : Real.log (594871730303 / 500000000000) = -Real.log (500000000000 / 594871730303) := by
    rw [show ((594871730303 / 500000000000) : ℝ) = ((500000000000 / 594871730303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3077_neg : (86914979 / 250000000) ≤ -Real.log (7812500000 / 11060552301) ∧
    -Real.log (7812500000 / 11060552301) ≤ (347659917 / 1000000000) := by
  have h := checkLog_sound (w := (3248052301 / 18873052301)) (n := 12)
    (lo := (86914979 / 250000000)) (hi := (347659917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11060552301 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11060552301 / 7812500000) = 1/(7812500000 / 11060552301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3077 : Bounds (86914979 / 250000000) (347659917 / 1000000000) (Real.log (11060552301 / 7812500000)) := by
  have h := reflection_log_3077_neg
  have he : Real.log (11060552301 / 7812500000) = -Real.log (7812500000 / 11060552301) := by
    rw [show ((11060552301 / 7812500000) : ℝ) = ((7812500000 / 11060552301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3078_neg : (43483253 / 125000000) ≤ -Real.log (20000000000 / 28320850447) ∧
    -Real.log (20000000000 / 28320850447) ≤ (13914641 / 40000000) := by
  have h := checkLog_sound (w := (8320850447 / 48320850447)) (n := 12)
    (lo := (43483253 / 125000000)) (hi := (13914641 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28320850447 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28320850447 / 20000000000) = 1/(20000000000 / 28320850447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3078 : Bounds (43483253 / 125000000) (13914641 / 40000000) (Real.log (28320850447 / 20000000000)) := by
  have h := reflection_log_3078_neg
  have he : Real.log (28320850447 / 20000000000) = -Real.log (20000000000 / 28320850447) := by
    rw [show ((28320850447 / 20000000000) : ℝ) = ((20000000000 / 28320850447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3079_neg : (158967631 / 1000000000) ≤ -Real.log (10000 / 11723) ∧
    -Real.log (10000 / 11723) ≤ (9935477 / 62500000) := by
  have h := checkLog_sound (w := (1723 / 21723)) (n := 12)
    (lo := (158967631 / 1000000000)) (hi := (9935477 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11723 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11723 / 10000) = 1/(10000 / 11723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3079 : Bounds (158967631 / 1000000000) (9935477 / 62500000) (Real.log (11723 / 10000)) := by
  have h := reflection_log_3079_neg
  have he : Real.log (11723 / 10000) = -Real.log (10000 / 11723) := by
    rw [show ((11723 / 10000) : ℝ) = ((10000 / 11723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3080_neg : (189104509 / 1000000000) ≤ -Real.log (8277 / 10000) ∧
    -Real.log (8277 / 10000) ≤ (18910451 / 100000000) := by
  have h := checkLog_sound (w := (1723 / 18277)) (n := 12)
    (lo := (189104509 / 1000000000)) (hi := (18910451 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8277) = 1/(8277 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3080 : Bounds (-18910451 / 100000000) (-189104509 / 1000000000) (Real.log (8277 / 10000)) := by
  have h := reflection_log_3080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3081_neg : (34457 / 200000000) ≤ -Real.log (10000000 / 10001723) ∧
    -Real.log (10000000 / 10001723) ≤ (86143 / 500000000) := by
  have h := checkLog_sound (w := (1723 / 20001723)) (n := 12)
    (lo := (34457 / 200000000)) (hi := (86143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001723 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001723 / 10000000) = 1/(10000000 / 10001723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3081 : Bounds (34457 / 200000000) (86143 / 500000000) (Real.log (10001723 / 10000000)) := by
  have h := reflection_log_3081_neg
  have he : Real.log (10001723 / 10000000) = -Real.log (10000000 / 10001723) := by
    rw [show ((10001723 / 10000000) : ℝ) = ((10000000 / 10001723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3082_neg : (86157 / 500000000) ≤ -Real.log (9998277 / 10000000) ∧
    -Real.log (9998277 / 10000000) ≤ (34463 / 200000000) := by
  have h := checkLog_sound (w := (1723 / 19998277)) (n := 12)
    (lo := (86157 / 500000000)) (hi := (34463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998277) = 1/(9998277 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3082 : Bounds (-34463 / 200000000) (-86157 / 500000000) (Real.log (9998277 / 10000000)) := by
  have h := reflection_log_3082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3083_neg : (10367659 / 125000000) ≤ -Real.log (500000 / 543239) ∧
    -Real.log (500000 / 543239) ≤ (82941273 / 1000000000) := by
  have h := checkLog_sound (w := (43239 / 1043239)) (n := 12)
    (lo := (10367659 / 125000000)) (hi := (82941273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543239 / 500000) = 1/(500000 / 543239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3083 : Bounds (10367659 / 125000000) (82941273 / 1000000000) (Real.log (543239 / 500000)) := by
  have h := reflection_log_3083_neg
  have he : Real.log (543239 / 500000) = -Real.log (500000 / 543239) := by
    rw [show ((543239 / 500000) : ℝ) = ((500000 / 543239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3084_neg : (4522391 / 50000000) ≤ -Real.log (456761 / 500000) ∧
    -Real.log (456761 / 500000) ≤ (90447821 / 1000000000) := by
  have h := checkLog_sound (w := (43239 / 956761)) (n := 12)
    (lo := (4522391 / 50000000)) (hi := (90447821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456761) = 1/(456761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3084 : Bounds (-90447821 / 1000000000) (-4522391 / 50000000) (Real.log (456761 / 500000)) := by
  have h := reflection_log_3084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3085_neg : (83146501 / 1000000000) ≤ -Real.log (1000000 / 1086701) ∧
    -Real.log (1000000 / 1086701) ≤ (41573251 / 500000000) := by
  have h := checkLog_sound (w := (86701 / 2086701)) (n := 12)
    (lo := (83146501 / 1000000000)) (hi := (41573251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086701 / 1000000) = 1/(1000000 / 1086701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3085 : Bounds (83146501 / 1000000000) (41573251 / 500000000) (Real.log (1086701 / 1000000)) := by
  have h := reflection_log_3085_neg
  have he : Real.log (1086701 / 1000000) = -Real.log (1000000 / 1086701) := by
    rw [show ((1086701 / 1000000) : ℝ) = ((1000000 / 1086701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3086_neg : (2267299 / 25000000) ≤ -Real.log (913299 / 1000000) ∧
    -Real.log (913299 / 1000000) ≤ (90691961 / 1000000000) := by
  have h := checkLog_sound (w := (86701 / 1913299)) (n := 12)
    (lo := (2267299 / 25000000)) (hi := (90691961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913299) = 1/(913299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3086 : Bounds (-90691961 / 1000000000) (-2267299 / 25000000) (Real.log (913299 / 1000000)) := by
  have h := reflection_log_3086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3087_neg : (3772729 / 500000000) ≤ -Real.log (992482936599 / 1000000000000) ∧
    -Real.log (992482936599 / 1000000000000) ≤ (7545459 / 1000000000) := by
  have h := checkLog_sound (w := (7517063401 / 1992482936599)) (n := 12)
    (lo := (3772729 / 500000000)) (hi := (7545459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992482936599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992482936599) = 1/(992482936599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3087 : Bounds (-7545459 / 1000000000) (-3772729 / 500000000) (Real.log (992482936599 / 1000000000000)) := by
  have h := reflection_log_3087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3088_neg : (1876637 / 250000000) ≤ -Real.log (248130388879 / 250000000000) ∧
    -Real.log (248130388879 / 250000000000) ≤ (7506549 / 1000000000) := by
  have h := checkLog_sound (w := (1869611121 / 498130388879)) (n := 12)
    (lo := (1876637 / 250000000)) (hi := (7506549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248130388879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248130388879) = 1/(248130388879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3088 : Bounds (-7506549 / 1000000000) (-1876637 / 250000000) (Real.log (248130388879 / 250000000000)) := by
  have h := reflection_log_3088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3089_neg : (43347273 / 250000000) ≤ -Real.log (100000000000 / 118932877369) ∧
    -Real.log (100000000000 / 118932877369) ≤ (173389093 / 1000000000) := by
  have h := checkLog_sound (w := (18932877369 / 218932877369)) (n := 12)
    (lo := (43347273 / 250000000)) (hi := (173389093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118932877369 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118932877369 / 100000000000) = 1/(100000000000 / 118932877369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3089 : Bounds (43347273 / 250000000) (173389093 / 1000000000) (Real.log (118932877369 / 100000000000)) := by
  have h := reflection_log_3089_neg
  have he : Real.log (118932877369 / 100000000000) = -Real.log (100000000000 / 118932877369) := by
    rw [show ((118932877369 / 100000000000) : ℝ) = ((100000000000 / 118932877369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3090_neg : (173838461 / 1000000000) ≤ -Real.log (50000000000 / 59493167079) ∧
    -Real.log (50000000000 / 59493167079) ≤ (86919231 / 500000000) := by
  have h := checkLog_sound (w := (9493167079 / 109493167079)) (n := 12)
    (lo := (173838461 / 1000000000)) (hi := (86919231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59493167079 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59493167079 / 50000000000) = 1/(50000000000 / 59493167079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3090 : Bounds (173838461 / 1000000000) (86919231 / 500000000) (Real.log (59493167079 / 50000000000)) := by
  have h := reflection_log_3090_neg
  have he : Real.log (59493167079 / 50000000000) = -Real.log (50000000000 / 59493167079) := by
    rw [show ((59493167079 / 50000000000) : ℝ) = ((50000000000 / 59493167079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3091_neg : (43483253 / 125000000) ≤ -Real.log (250000000000 / 354010630587) ∧
    -Real.log (250000000000 / 354010630587) ≤ (13914641 / 40000000) := by
  have h := checkLog_sound (w := (104010630587 / 604010630587)) (n := 12)
    (lo := (43483253 / 125000000)) (hi := (13914641 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354010630587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354010630587 / 250000000000) = 1/(250000000000 / 354010630587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3091 : Bounds (43483253 / 125000000) (13914641 / 40000000) (Real.log (354010630587 / 250000000000)) := by
  have h := reflection_log_3091_neg
  have he : Real.log (354010630587 / 250000000000) = -Real.log (250000000000 / 354010630587) := by
    rw [show ((354010630587 / 250000000000) : ℝ) = ((250000000000 / 354010630587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3092_neg : (17403607 / 50000000) ≤ -Real.log (250000000000 / 354083605171) ∧
    -Real.log (250000000000 / 354083605171) ≤ (348072141 / 1000000000) := by
  have h := checkLog_sound (w := (104083605171 / 604083605171)) (n := 12)
    (lo := (17403607 / 50000000)) (hi := (348072141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354083605171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354083605171 / 250000000000) = 1/(250000000000 / 354083605171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3092 : Bounds (17403607 / 50000000) (348072141 / 1000000000) (Real.log (354083605171 / 250000000000)) := by
  have h := reflection_log_3092_neg
  have he : Real.log (354083605171 / 250000000000) = -Real.log (250000000000 / 354083605171) := by
    rw [show ((354083605171 / 250000000000) : ℝ) = ((250000000000 / 354083605171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3093_neg : (159052929 / 1000000000) ≤ -Real.log (2500 / 2931) ∧
    -Real.log (2500 / 2931) ≤ (15905293 / 100000000) := by
  have h := checkLog_sound (w := (431 / 5431)) (n := 12)
    (lo := (159052929 / 1000000000)) (hi := (15905293 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2931 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2931 / 2500) = 1/(2500 / 2931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3093 : Bounds (159052929 / 1000000000) (15905293 / 100000000) (Real.log (2931 / 2500)) := by
  have h := reflection_log_3093_neg
  have he : Real.log (2931 / 2500) = -Real.log (2500 / 2931) := by
    rw [show ((2931 / 2500) : ℝ) = ((2500 / 2931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3094_neg : (189225333 / 1000000000) ≤ -Real.log (2069 / 2500) ∧
    -Real.log (2069 / 2500) ≤ (94612667 / 500000000) := by
  have h := checkLog_sound (w := (431 / 4569)) (n := 12)
    (lo := (189225333 / 1000000000)) (hi := (94612667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2069) = 1/(2069 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3094 : Bounds (-94612667 / 500000000) (-189225333 / 1000000000) (Real.log (2069 / 2500)) := by
  have h := reflection_log_3094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3095_neg : (34477 / 200000000) ≤ -Real.log (2500000 / 2500431) ∧
    -Real.log (2500000 / 2500431) ≤ (86193 / 500000000) := by
  have h := checkLog_sound (w := (431 / 5000431)) (n := 12)
    (lo := (34477 / 200000000)) (hi := (86193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500431 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500431 / 2500000) = 1/(2500000 / 2500431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3095 : Bounds (34477 / 200000000) (86193 / 500000000) (Real.log (2500431 / 2500000)) := by
  have h := reflection_log_3095_neg
  have he : Real.log (2500431 / 2500000) = -Real.log (2500000 / 2500431) := by
    rw [show ((2500431 / 2500000) : ℝ) = ((2500000 / 2500431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3096_neg : (86207 / 500000000) ≤ -Real.log (2499569 / 2500000) ∧
    -Real.log (2499569 / 2500000) ≤ (34483 / 200000000) := by
  have h := checkLog_sound (w := (431 / 4999569)) (n := 12)
    (lo := (86207 / 500000000)) (hi := (34483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499569) = 1/(2499569 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3096 : Bounds (-34483 / 200000000) (-86207 / 500000000) (Real.log (2499569 / 2500000)) := by
  have h := reflection_log_3096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3097_neg : (82988211 / 1000000000) ≤ -Real.log (1000000 / 1086529) ∧
    -Real.log (1000000 / 1086529) ≤ (20747053 / 250000000) := by
  have h := checkLog_sound (w := (86529 / 2086529)) (n := 12)
    (lo := (82988211 / 1000000000)) (hi := (20747053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086529 / 1000000) = 1/(1000000 / 1086529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3097 : Bounds (82988211 / 1000000000) (20747053 / 250000000) (Real.log (1086529 / 1000000)) := by
  have h := reflection_log_3097_neg
  have he : Real.log (1086529 / 1000000) = -Real.log (1000000 / 1086529) := by
    rw [show ((1086529 / 1000000) : ℝ) = ((1000000 / 1086529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3098_neg : (90503649 / 1000000000) ≤ -Real.log (913471 / 1000000) ∧
    -Real.log (913471 / 1000000) ≤ (1810073 / 20000000) := by
  have h := checkLog_sound (w := (86529 / 1913471)) (n := 12)
    (lo := (90503649 / 1000000000)) (hi := (1810073 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913471) = 1/(913471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3098 : Bounds (-1810073 / 20000000) (-90503649 / 1000000000) (Real.log (913471 / 1000000)) := by
  have h := reflection_log_3098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3099_neg : (83193431 / 1000000000) ≤ -Real.log (31250 / 33961) ∧
    -Real.log (31250 / 33961) ≤ (10399179 / 125000000) := by
  have h := checkLog_sound (w := (2711 / 65211)) (n := 12)
    (lo := (83193431 / 1000000000)) (hi := (10399179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33961 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33961 / 31250) = 1/(31250 / 33961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3099 : Bounds (83193431 / 1000000000) (10399179 / 125000000) (Real.log (33961 / 31250)) := by
  have h := reflection_log_3099_neg
  have he : Real.log (33961 / 31250) = -Real.log (31250 / 33961) := by
    rw [show ((33961 / 31250) : ℝ) = ((31250 / 33961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3100_neg : (90747803 / 1000000000) ≤ -Real.log (28539 / 31250) ∧
    -Real.log (28539 / 31250) ≤ (22686951 / 250000000) := by
  have h := checkLog_sound (w := (2711 / 59789)) (n := 12)
    (lo := (90747803 / 1000000000)) (hi := (22686951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28539) = 1/(28539 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3100 : Bounds (-22686951 / 250000000) (-90747803 / 1000000000) (Real.log (28539 / 31250)) := by
  have h := reflection_log_3100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3101_neg : (1888593 / 250000000) ≤ -Real.log (969212979 / 976562500) ∧
    -Real.log (969212979 / 976562500) ≤ (7554373 / 1000000000) := by
  have h := checkLog_sound (w := (7349521 / 1945775479)) (n := 12)
    (lo := (1888593 / 250000000)) (hi := (7554373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969212979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969212979) = 1/(969212979 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3101 : Bounds (-7554373 / 1000000000) (-1888593 / 250000000) (Real.log (969212979 / 976562500)) := by
  have h := reflection_log_3101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3102_neg : (3757719 / 500000000) ≤ -Real.log (992512732159 / 1000000000000) ∧
    -Real.log (992512732159 / 1000000000000) ≤ (7515439 / 1000000000) := by
  have h := checkLog_sound (w := (7487267841 / 1992512732159)) (n := 12)
    (lo := (3757719 / 500000000)) (hi := (7515439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992512732159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992512732159) = 1/(992512732159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3102 : Bounds (-7515439 / 1000000000) (-3757719 / 500000000) (Real.log (992512732159 / 1000000000000)) := by
  have h := reflection_log_3102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3103_neg : (173491861 / 1000000000) ≤ -Real.log (500000000000 / 594725503053) ∧
    -Real.log (500000000000 / 594725503053) ≤ (86745931 / 500000000) := by
  have h := checkLog_sound (w := (94725503053 / 1094725503053)) (n := 12)
    (lo := (173491861 / 1000000000)) (hi := (86745931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594725503053 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594725503053 / 500000000000) = 1/(500000000000 / 594725503053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3103 : Bounds (173491861 / 1000000000) (86745931 / 500000000) (Real.log (594725503053 / 500000000000)) := by
  have h := reflection_log_3103_neg
  have he : Real.log (594725503053 / 500000000000) = -Real.log (500000000000 / 594725503053) := by
    rw [show ((594725503053 / 500000000000) : ℝ) = ((500000000000 / 594725503053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3104_neg : (86970617 / 500000000) ≤ -Real.log (31250000000 / 37187051053) ∧
    -Real.log (31250000000 / 37187051053) ≤ (34788247 / 200000000) := by
  have h := checkLog_sound (w := (5937051053 / 68437051053)) (n := 12)
    (lo := (86970617 / 500000000)) (hi := (34788247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37187051053 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37187051053 / 31250000000) = 1/(31250000000 / 37187051053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3104 : Bounds (86970617 / 500000000) (34788247 / 200000000) (Real.log (37187051053 / 31250000000)) := by
  have h := reflection_log_3104_neg
  have he : Real.log (37187051053 / 31250000000) = -Real.log (31250000000 / 37187051053) := by
    rw [show ((37187051053 / 31250000000) : ℝ) = ((31250000000 / 37187051053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3105_neg : (17403607 / 50000000) ≤ -Real.log (500000000000 / 708167210341) ∧
    -Real.log (500000000000 / 708167210341) ≤ (348072141 / 1000000000) := by
  have h := checkLog_sound (w := (208167210341 / 1208167210341)) (n := 12)
    (lo := (17403607 / 50000000)) (hi := (348072141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708167210341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708167210341 / 500000000000) = 1/(500000000000 / 708167210341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3105 : Bounds (17403607 / 50000000) (348072141 / 1000000000) (Real.log (708167210341 / 500000000000)) := by
  have h := reflection_log_3105_neg
  have he : Real.log (708167210341 / 500000000000) = -Real.log (500000000000 / 708167210341) := by
    rw [show ((708167210341 / 500000000000) : ℝ) = ((500000000000 / 708167210341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3106_neg : (174139131 / 500000000) ≤ -Real.log (500000000000 / 708313194781) ∧
    -Real.log (500000000000 / 708313194781) ≤ (348278263 / 1000000000) := by
  have h := checkLog_sound (w := (208313194781 / 1208313194781)) (n := 12)
    (lo := (174139131 / 500000000)) (hi := (348278263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708313194781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708313194781 / 500000000000) = 1/(500000000000 / 708313194781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3106 : Bounds (174139131 / 500000000) (348278263 / 1000000000) (Real.log (708313194781 / 500000000000)) := by
  have h := reflection_log_3106_neg
  have he : Real.log (708313194781 / 500000000000) = -Real.log (500000000000 / 708313194781) := by
    rw [show ((708313194781 / 500000000000) : ℝ) = ((500000000000 / 708313194781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3107_neg : (159138221 / 1000000000) ≤ -Real.log (400 / 469) ∧
    -Real.log (400 / 469) ≤ (79569111 / 500000000) := by
  have h := checkLog_sound (w := (69 / 869)) (n := 12)
    (lo := (159138221 / 1000000000)) (hi := (79569111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469 / 400) = 1/(400 / 469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3107 : Bounds (159138221 / 1000000000) (79569111 / 500000000) (Real.log (469 / 400)) := by
  have h := reflection_log_3107_neg
  have he : Real.log (469 / 400) = -Real.log (400 / 469) := by
    rw [show ((469 / 400) : ℝ) = ((400 / 469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3108_neg : (189346171 / 1000000000) ≤ -Real.log (331 / 400) ∧
    -Real.log (331 / 400) ≤ (47336543 / 250000000) := by
  have h := checkLog_sound (w := (69 / 731)) (n := 12)
    (lo := (189346171 / 1000000000)) (hi := (47336543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 331) = 1/(331 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3108 : Bounds (-47336543 / 250000000) (-189346171 / 1000000000) (Real.log (331 / 400)) := by
  have h := reflection_log_3108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3109_neg : (34497 / 200000000) ≤ -Real.log (400000 / 400069) ∧
    -Real.log (400000 / 400069) ≤ (86243 / 500000000) := by
  have h := checkLog_sound (w := (69 / 800069)) (n := 12)
    (lo := (34497 / 200000000)) (hi := (86243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400069 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400069 / 400000) = 1/(400000 / 400069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3109 : Bounds (34497 / 200000000) (86243 / 500000000) (Real.log (400069 / 400000)) := by
  have h := reflection_log_3109_neg
  have he : Real.log (400069 / 400000) = -Real.log (400000 / 400069) := by
    rw [show ((400069 / 400000) : ℝ) = ((400000 / 400069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3110_neg : (86257 / 500000000) ≤ -Real.log (399931 / 400000) ∧
    -Real.log (399931 / 400000) ≤ (34503 / 200000000) := by
  have h := checkLog_sound (w := (69 / 799931)) (n := 12)
    (lo := (86257 / 500000000)) (hi := (34503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399931) = 1/(399931 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3110 : Bounds (-34503 / 200000000) (-86257 / 500000000) (Real.log (399931 / 400000)) := by
  have h := reflection_log_3110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3111_neg : (20758787 / 250000000) ≤ -Real.log (50000 / 54329) ∧
    -Real.log (50000 / 54329) ≤ (83035149 / 1000000000) := by
  have h := checkLog_sound (w := (4329 / 104329)) (n := 12)
    (lo := (20758787 / 250000000)) (hi := (83035149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54329 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54329 / 50000) = 1/(50000 / 54329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3111 : Bounds (20758787 / 250000000) (83035149 / 1000000000) (Real.log (54329 / 50000)) := by
  have h := reflection_log_3111_neg
  have he : Real.log (54329 / 50000) = -Real.log (50000 / 54329) := by
    rw [show ((54329 / 50000) : ℝ) = ((50000 / 54329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3112_neg : (45279741 / 500000000) ≤ -Real.log (45671 / 50000) ∧
    -Real.log (45671 / 50000) ≤ (90559483 / 1000000000) := by
  have h := checkLog_sound (w := (4329 / 95671)) (n := 12)
    (lo := (45279741 / 500000000)) (hi := (90559483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45671) = 1/(45671 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3112 : Bounds (-90559483 / 1000000000) (-45279741 / 500000000) (Real.log (45671 / 50000)) := by
  have h := reflection_log_3112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3113_neg : (41620179 / 500000000) ≤ -Real.log (1000000 / 1086803) ∧
    -Real.log (1000000 / 1086803) ≤ (83240359 / 1000000000) := by
  have h := checkLog_sound (w := (86803 / 2086803)) (n := 12)
    (lo := (41620179 / 500000000)) (hi := (83240359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086803 / 1000000) = 1/(1000000 / 1086803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3113 : Bounds (41620179 / 500000000) (83240359 / 1000000000) (Real.log (1086803 / 1000000)) := by
  have h := reflection_log_3113_neg
  have he : Real.log (1086803 / 1000000) = -Real.log (1000000 / 1086803) := by
    rw [show ((1086803 / 1000000) : ℝ) = ((1000000 / 1086803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3114_neg : (90803649 / 1000000000) ≤ -Real.log (913197 / 1000000) ∧
    -Real.log (913197 / 1000000) ≤ (1816073 / 20000000) := by
  have h := checkLog_sound (w := (86803 / 1913197)) (n := 12)
    (lo := (90803649 / 1000000000)) (hi := (1816073 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913197) = 1/(913197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3114 : Bounds (-1816073 / 20000000) (-90803649 / 1000000000) (Real.log (913197 / 1000000)) := by
  have h := reflection_log_3114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3115_neg : (756329 / 100000000) ≤ -Real.log (992465239191 / 1000000000000) ∧
    -Real.log (992465239191 / 1000000000000) ≤ (7563291 / 1000000000) := by
  have h := checkLog_sound (w := (7534760809 / 1992465239191)) (n := 12)
    (lo := (756329 / 100000000)) (hi := (7563291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992465239191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992465239191) = 1/(992465239191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3115 : Bounds (-7563291 / 1000000000) (-756329 / 100000000) (Real.log (992465239191 / 1000000000000)) := by
  have h := reflection_log_3115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3116_neg : (7524333 / 1000000000) ≤ -Real.log (2481259759 / 2500000000) ∧
    -Real.log (2481259759 / 2500000000) ≤ (3762167 / 500000000) := by
  have h := checkLog_sound (w := (18740241 / 4981259759)) (n := 12)
    (lo := (7524333 / 1000000000)) (hi := (3762167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2481259759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2481259759) = 1/(2481259759 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3116 : Bounds (-3762167 / 500000000) (-7524333 / 1000000000) (Real.log (2481259759 / 2500000000)) := by
  have h := reflection_log_3116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3117_neg : (173594631 / 1000000000) ≤ -Real.log (250000000000 / 297393313043) ∧
    -Real.log (250000000000 / 297393313043) ≤ (21699329 / 125000000) := by
  have h := checkLog_sound (w := (47393313043 / 547393313043)) (n := 12)
    (lo := (173594631 / 1000000000)) (hi := (21699329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297393313043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297393313043 / 250000000000) = 1/(250000000000 / 297393313043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3117 : Bounds (173594631 / 1000000000) (21699329 / 125000000) (Real.log (297393313043 / 250000000000)) := by
  have h := reflection_log_3117_neg
  have he : Real.log (297393313043 / 250000000000) = -Real.log (250000000000 / 297393313043) := by
    rw [show ((297393313043 / 250000000000) : ℝ) = ((250000000000 / 297393313043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3118_neg : (21755501 / 125000000) ≤ -Real.log (100000000000 / 119010793947) ∧
    -Real.log (100000000000 / 119010793947) ≤ (174044009 / 1000000000) := by
  have h := checkLog_sound (w := (19010793947 / 219010793947)) (n := 12)
    (lo := (21755501 / 125000000)) (hi := (174044009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119010793947 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119010793947 / 100000000000) = 1/(100000000000 / 119010793947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3118 : Bounds (21755501 / 125000000) (174044009 / 1000000000) (Real.log (119010793947 / 100000000000)) := by
  have h := reflection_log_3118_neg
  have he : Real.log (119010793947 / 100000000000) = -Real.log (100000000000 / 119010793947) := by
    rw [show ((119010793947 / 100000000000) : ℝ) = ((100000000000 / 119010793947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3119_neg : (174139131 / 500000000) ≤ -Real.log (25000000000 / 35415659739) ∧
    -Real.log (25000000000 / 35415659739) ≤ (348278263 / 1000000000) := by
  have h := checkLog_sound (w := (10415659739 / 60415659739)) (n := 12)
    (lo := (174139131 / 500000000)) (hi := (348278263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35415659739 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35415659739 / 25000000000) = 1/(25000000000 / 35415659739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3119 : Bounds (174139131 / 500000000) (348278263 / 1000000000) (Real.log (35415659739 / 25000000000)) := by
  have h := reflection_log_3119_neg
  have he : Real.log (35415659739 / 25000000000) = -Real.log (25000000000 / 35415659739) := by
    rw [show ((35415659739 / 25000000000) : ℝ) = ((25000000000 / 35415659739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3120_neg : (348484393 / 1000000000) ≤ -Real.log (250000000000 / 354229607251) ∧
    -Real.log (250000000000 / 354229607251) ≤ (174242197 / 500000000) := by
  have h := checkLog_sound (w := (104229607251 / 604229607251)) (n := 12)
    (lo := (348484393 / 1000000000)) (hi := (174242197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354229607251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354229607251 / 250000000000) = 1/(250000000000 / 354229607251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3120 : Bounds (348484393 / 1000000000) (174242197 / 500000000) (Real.log (354229607251 / 250000000000)) := by
  have h := reflection_log_3120_neg
  have he : Real.log (354229607251 / 250000000000) = -Real.log (250000000000 / 354229607251) := by
    rw [show ((354229607251 / 250000000000) : ℝ) = ((250000000000 / 354229607251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3121_neg : (31844701 / 200000000) ≤ -Real.log (5000 / 5863) ∧
    -Real.log (5000 / 5863) ≤ (79611753 / 500000000) := by
  have h := checkLog_sound (w := (863 / 10863)) (n := 12)
    (lo := (31844701 / 200000000)) (hi := (79611753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5863 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5863 / 5000) = 1/(5000 / 5863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3121 : Bounds (31844701 / 200000000) (79611753 / 500000000) (Real.log (5863 / 5000)) := by
  have h := reflection_log_3121_neg
  have he : Real.log (5863 / 5000) = -Real.log (5000 / 5863) := by
    rw [show ((5863 / 5000) : ℝ) = ((5000 / 5863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3122_neg : (11841689 / 62500000) ≤ -Real.log (4137 / 5000) ∧
    -Real.log (4137 / 5000) ≤ (7578681 / 40000000) := by
  have h := checkLog_sound (w := (863 / 9137)) (n := 12)
    (lo := (11841689 / 62500000)) (hi := (7578681 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4137) = 1/(4137 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3122 : Bounds (-7578681 / 40000000) (-11841689 / 62500000) (Real.log (4137 / 5000)) := by
  have h := reflection_log_3122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3123_neg : (34517 / 200000000) ≤ -Real.log (5000000 / 5000863) ∧
    -Real.log (5000000 / 5000863) ≤ (86293 / 500000000) := by
  have h := checkLog_sound (w := (863 / 10000863)) (n := 12)
    (lo := (34517 / 200000000)) (hi := (86293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000863 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000863 / 5000000) = 1/(5000000 / 5000863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3123 : Bounds (34517 / 200000000) (86293 / 500000000) (Real.log (5000863 / 5000000)) := by
  have h := reflection_log_3123_neg
  have he : Real.log (5000863 / 5000000) = -Real.log (5000000 / 5000863) := by
    rw [show ((5000863 / 5000000) : ℝ) = ((5000000 / 5000863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3124_neg : (86307 / 500000000) ≤ -Real.log (4999137 / 5000000) ∧
    -Real.log (4999137 / 5000000) ≤ (34523 / 200000000) := by
  have h := checkLog_sound (w := (863 / 9999137)) (n := 12)
    (lo := (86307 / 500000000)) (hi := (34523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999137) = 1/(4999137 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3124 : Bounds (-34523 / 200000000) (-86307 / 500000000) (Real.log (4999137 / 5000000)) := by
  have h := reflection_log_3124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3125_neg : (20770521 / 250000000) ≤ -Real.log (1000000 / 1086631) ∧
    -Real.log (1000000 / 1086631) ≤ (16616417 / 200000000) := by
  have h := checkLog_sound (w := (86631 / 2086631)) (n := 12)
    (lo := (20770521 / 250000000)) (hi := (16616417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086631 / 1000000) = 1/(1000000 / 1086631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3125 : Bounds (20770521 / 250000000) (16616417 / 200000000) (Real.log (1086631 / 1000000)) := by
  have h := reflection_log_3125_neg
  have he : Real.log (1086631 / 1000000) = -Real.log (1000000 / 1086631) := by
    rw [show ((1086631 / 1000000) : ℝ) = ((1000000 / 1086631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3126_neg : (90615317 / 1000000000) ≤ -Real.log (913369 / 1000000) ∧
    -Real.log (913369 / 1000000) ≤ (45307659 / 500000000) := by
  have h := checkLog_sound (w := (86631 / 1913369)) (n := 12)
    (lo := (90615317 / 1000000000)) (hi := (45307659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913369) = 1/(913369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3126 : Bounds (-45307659 / 500000000) (-90615317 / 1000000000) (Real.log (913369 / 1000000)) := by
  have h := reflection_log_3126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3127_neg : (20821821 / 250000000) ≤ -Real.log (500000 / 543427) ∧
    -Real.log (500000 / 543427) ≤ (16657457 / 200000000) := by
  have h := checkLog_sound (w := (43427 / 1043427)) (n := 12)
    (lo := (20821821 / 250000000)) (hi := (16657457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543427 / 500000) = 1/(500000 / 543427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3127 : Bounds (20821821 / 250000000) (16657457 / 200000000) (Real.log (543427 / 500000)) := by
  have h := reflection_log_3127_neg
  have he : Real.log (543427 / 500000) = -Real.log (500000 / 543427) := by
    rw [show ((543427 / 500000) : ℝ) = ((500000 / 543427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3128_neg : (45429749 / 500000000) ≤ -Real.log (456573 / 500000) ∧
    -Real.log (456573 / 500000) ≤ (90859499 / 1000000000) := by
  have h := checkLog_sound (w := (43427 / 956573)) (n := 12)
    (lo := (45429749 / 500000000)) (hi := (90859499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456573) = 1/(456573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3128 : Bounds (-90859499 / 1000000000) (-45429749 / 500000000) (Real.log (456573 / 500000)) := by
  have h := reflection_log_3128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3129_neg : (3786107 / 500000000) ≤ -Real.log (248114095671 / 250000000000) ∧
    -Real.log (248114095671 / 250000000000) ≤ (1514443 / 200000000) := by
  have h := checkLog_sound (w := (1885904329 / 498114095671)) (n := 12)
    (lo := (3786107 / 500000000)) (hi := (1514443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248114095671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248114095671) = 1/(248114095671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3129 : Bounds (-1514443 / 200000000) (-3786107 / 500000000) (Real.log (248114095671 / 250000000000)) := by
  have h := reflection_log_3129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3130_neg : (7533233 / 1000000000) ≤ -Real.log (992495069839 / 1000000000000) ∧
    -Real.log (992495069839 / 1000000000000) ≤ (3766617 / 500000000) := by
  have h := checkLog_sound (w := (7504930161 / 1992495069839)) (n := 12)
    (lo := (7533233 / 1000000000)) (hi := (3766617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992495069839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992495069839) = 1/(992495069839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3130 : Bounds (-3766617 / 500000000) (-7533233 / 1000000000) (Real.log (992495069839 / 1000000000000)) := by
  have h := reflection_log_3130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3131_neg : (86848701 / 500000000) ≤ -Real.log (100000000000 / 118969551189) ∧
    -Real.log (100000000000 / 118969551189) ≤ (173697403 / 1000000000) := by
  have h := checkLog_sound (w := (18969551189 / 218969551189)) (n := 12)
    (lo := (86848701 / 500000000)) (hi := (173697403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118969551189 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118969551189 / 100000000000) = 1/(100000000000 / 118969551189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3131 : Bounds (86848701 / 500000000) (173697403 / 1000000000) (Real.log (118969551189 / 100000000000)) := by
  have h := reflection_log_3131_neg
  have he : Real.log (118969551189 / 100000000000) = -Real.log (100000000000 / 118969551189) := by
    rw [show ((118969551189 / 100000000000) : ℝ) = ((100000000000 / 118969551189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3132_neg : (174146783 / 1000000000) ≤ -Real.log (250000000000 / 297557564727) ∧
    -Real.log (250000000000 / 297557564727) ≤ (5442087 / 31250000) := by
  have h := checkLog_sound (w := (47557564727 / 547557564727)) (n := 12)
    (lo := (174146783 / 1000000000)) (hi := (5442087 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297557564727 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297557564727 / 250000000000) = 1/(250000000000 / 297557564727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3132 : Bounds (174146783 / 1000000000) (5442087 / 31250000) (Real.log (297557564727 / 250000000000)) := by
  have h := reflection_log_3132_neg
  have he : Real.log (297557564727 / 250000000000) = -Real.log (250000000000 / 297557564727) := by
    rw [show ((297557564727 / 250000000000) : ℝ) = ((250000000000 / 297557564727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3133_neg : (348484393 / 1000000000) ≤ -Real.log (500000000000 / 708459214501) ∧
    -Real.log (500000000000 / 708459214501) ≤ (174242197 / 500000000) := by
  have h := checkLog_sound (w := (208459214501 / 1208459214501)) (n := 12)
    (lo := (348484393 / 1000000000)) (hi := (174242197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708459214501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708459214501 / 500000000000) = 1/(500000000000 / 708459214501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3133 : Bounds (348484393 / 1000000000) (174242197 / 500000000) (Real.log (708459214501 / 500000000000)) := by
  have h := reflection_log_3133_neg
  have he : Real.log (708459214501 / 500000000000) = -Real.log (500000000000 / 708459214501) := by
    rw [show ((708459214501 / 500000000000) : ℝ) = ((500000000000 / 708459214501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3134_neg : (34869053 / 100000000) ≤ -Real.log (500000000000 / 708605269519) ∧
    -Real.log (500000000000 / 708605269519) ≤ (348690531 / 1000000000) := by
  have h := checkLog_sound (w := (208605269519 / 1208605269519)) (n := 12)
    (lo := (34869053 / 100000000)) (hi := (348690531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708605269519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708605269519 / 500000000000) = 1/(500000000000 / 708605269519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3134 : Bounds (34869053 / 100000000) (348690531 / 1000000000) (Real.log (708605269519 / 500000000000)) := by
  have h := reflection_log_3134_neg
  have he : Real.log (708605269519 / 500000000000) = -Real.log (500000000000 / 708605269519) := by
    rw [show ((708605269519 / 500000000000) : ℝ) = ((500000000000 / 708605269519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3135_neg : (79654391 / 500000000) ≤ -Real.log (10000 / 11727) ∧
    -Real.log (10000 / 11727) ≤ (159308783 / 1000000000) := by
  have h := checkLog_sound (w := (1727 / 21727)) (n := 12)
    (lo := (79654391 / 500000000)) (hi := (159308783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11727 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11727 / 10000) = 1/(10000 / 11727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3135 : Bounds (79654391 / 500000000) (159308783 / 1000000000) (Real.log (11727 / 10000)) := by
  have h := reflection_log_3135_neg
  have he : Real.log (11727 / 10000) = -Real.log (10000 / 11727) := by
    rw [show ((11727 / 10000) : ℝ) = ((10000 / 11727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


