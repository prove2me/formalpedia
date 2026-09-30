-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0065__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0065__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:43:52.092189+00:00
-- url     : https://prove2.me/theorems/d442be80-7e4f-40f3-83dd-139987114a03
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0065 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0066)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0065 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0066)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0065 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0066)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0065 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0066) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0065 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0066).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0065 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4160_neg : (11251 / 62500000) ≤ -Real.log (49991 / 50000) ∧
    -Real.log (49991 / 50000) ≤ (180017 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 99991)) (n := 12)
    (lo := (11251 / 62500000)) (hi := (180017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49991) = 1/(49991 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4160 : Bounds (-180017 / 1000000000) (-11251 / 62500000) (Real.log (49991 / 50000)) := by
  have h := reflection_log_4160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4161_neg : (8653543 / 100000000) ≤ -Real.log (100000 / 109039) ∧
    -Real.log (100000 / 109039) ≤ (86535431 / 1000000000) := by
  have h := checkLog_sound (w := (9039 / 209039)) (n := 12)
    (lo := (8653543 / 100000000)) (hi := (86535431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109039 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109039 / 100000) = 1/(100000 / 109039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4161 : Bounds (8653543 / 100000000) (86535431 / 1000000000) (Real.log (109039 / 100000)) := by
  have h := reflection_log_4161_neg
  have he : Real.log (109039 / 100000) = -Real.log (100000 / 109039) := by
    rw [show ((109039 / 100000) : ℝ) = ((100000 / 109039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4162_neg : (47369671 / 500000000) ≤ -Real.log (90961 / 100000) ∧
    -Real.log (90961 / 100000) ≤ (94739343 / 1000000000) := by
  have h := checkLog_sound (w := (9039 / 190961)) (n := 12)
    (lo := (47369671 / 500000000)) (hi := (94739343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90961) = 1/(90961 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4162 : Bounds (-94739343 / 1000000000) (-47369671 / 500000000) (Real.log (90961 / 100000)) := by
  have h := reflection_log_4162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4163_neg : (43373629 / 500000000) ≤ -Real.log (1000000 / 1090621) ∧
    -Real.log (1000000 / 1090621) ≤ (86747259 / 1000000000) := by
  have h := checkLog_sound (w := (90621 / 2090621)) (n := 12)
    (lo := (43373629 / 500000000)) (hi := (86747259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090621 / 1000000) = 1/(1000000 / 1090621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4163 : Bounds (43373629 / 500000000) (86747259 / 1000000000) (Real.log (1090621 / 1000000)) := by
  have h := reflection_log_4163_neg
  have he : Real.log (1090621 / 1000000) = -Real.log (1000000 / 1090621) := by
    rw [show ((1090621 / 1000000) : ℝ) = ((1000000 / 1090621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4164_neg : (9499333 / 100000000) ≤ -Real.log (909379 / 1000000) ∧
    -Real.log (909379 / 1000000) ≤ (94993331 / 1000000000) := by
  have h := checkLog_sound (w := (90621 / 1909379)) (n := 12)
    (lo := (9499333 / 100000000)) (hi := (94993331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909379) = 1/(909379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4164 : Bounds (-94993331 / 1000000000) (-9499333 / 100000000) (Real.log (909379 / 1000000)) := by
  have h := reflection_log_4164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4165_neg : (8246071 / 1000000000) ≤ -Real.log (991787834359 / 1000000000000) ∧
    -Real.log (991787834359 / 1000000000000) ≤ (1030759 / 125000000) := by
  have h := checkLog_sound (w := (8212165641 / 1991787834359)) (n := 12)
    (lo := (8246071 / 1000000000)) (hi := (1030759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991787834359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991787834359) = 1/(991787834359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4165 : Bounds (-1030759 / 125000000) (-8246071 / 1000000000) (Real.log (991787834359 / 1000000000000)) := by
  have h := reflection_log_4165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4166_neg : (1025489 / 125000000) ≤ -Real.log (9918296479 / 10000000000) ∧
    -Real.log (9918296479 / 10000000000) ≤ (8203913 / 1000000000) := by
  have h := checkLog_sound (w := (81703521 / 19918296479)) (n := 12)
    (lo := (1025489 / 125000000)) (hi := (8203913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9918296479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9918296479) = 1/(9918296479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4166 : Bounds (-8203913 / 1000000000) (-1025489 / 125000000) (Real.log (9918296479 / 10000000000)) := by
  have h := reflection_log_4166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4167_neg : (181274773 / 1000000000) ≤ -Real.log (12500000000 / 14984306461) ∧
    -Real.log (12500000000 / 14984306461) ≤ (90637387 / 500000000) := by
  have h := checkLog_sound (w := (2484306461 / 27484306461)) (n := 12)
    (lo := (181274773 / 1000000000)) (hi := (90637387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14984306461 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14984306461 / 12500000000) = 1/(12500000000 / 14984306461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4167 : Bounds (181274773 / 1000000000) (90637387 / 500000000) (Real.log (14984306461 / 12500000000)) := by
  have h := reflection_log_4167_neg
  have he : Real.log (14984306461 / 12500000000) = -Real.log (12500000000 / 14984306461) := by
    rw [show ((14984306461 / 12500000000) : ℝ) = ((12500000000 / 14984306461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4168_neg : (45435147 / 250000000) ≤ -Real.log (250000000000 / 299825760217) ∧
    -Real.log (250000000000 / 299825760217) ≤ (181740589 / 1000000000) := by
  have h := checkLog_sound (w := (49825760217 / 549825760217)) (n := 12)
    (lo := (45435147 / 250000000)) (hi := (181740589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299825760217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299825760217 / 250000000000) = 1/(250000000000 / 299825760217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4168 : Bounds (45435147 / 250000000) (181740589 / 1000000000) (Real.log (299825760217 / 250000000000)) := by
  have h := reflection_log_4168_neg
  have he : Real.log (299825760217 / 250000000000) = -Real.log (250000000000 / 299825760217) := by
    rw [show ((299825760217 / 250000000000) : ℝ) = ((250000000000 / 299825760217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4169_neg : (90939671 / 250000000) ≤ -Real.log (500000000000 / 719363492257) ∧
    -Real.log (500000000000 / 719363492257) ≤ (72751737 / 200000000) := by
  have h := checkLog_sound (w := (219363492257 / 1219363492257)) (n := 12)
    (lo := (90939671 / 250000000)) (hi := (72751737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719363492257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719363492257 / 500000000000) = 1/(500000000000 / 719363492257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4169 : Bounds (90939671 / 250000000) (72751737 / 200000000) (Real.log (719363492257 / 500000000000)) := by
  have h := reflection_log_4169_neg
  have he : Real.log (719363492257 / 500000000000) = -Real.log (500000000000 / 719363492257) := by
    rw [show ((719363492257 / 500000000000) : ℝ) = ((500000000000 / 719363492257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4170_neg : (363965377 / 1000000000) ≤ -Real.log (250000000000 / 359756097561) ∧
    -Real.log (250000000000 / 359756097561) ≤ (181982689 / 500000000) := by
  have h := checkLog_sound (w := (109756097561 / 609756097561)) (n := 12)
    (lo := (363965377 / 1000000000)) (hi := (181982689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359756097561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359756097561 / 250000000000) = 1/(250000000000 / 359756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4170 : Bounds (363965377 / 1000000000) (181982689 / 500000000) (Real.log (359756097561 / 250000000000)) := by
  have h := reflection_log_4170_neg
  have he : Real.log (359756097561 / 250000000000) = -Real.log (250000000000 / 359756097561) := by
    rw [show ((359756097561 / 250000000000) : ℝ) = ((250000000000 / 359756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4171_neg : (8279959 / 50000000) ≤ -Real.log (10000 / 11801) ∧
    -Real.log (10000 / 11801) ≤ (165599181 / 1000000000) := by
  have h := checkLog_sound (w := (1801 / 21801)) (n := 12)
    (lo := (8279959 / 50000000)) (hi := (165599181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11801 / 10000) = 1/(10000 / 11801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4171 : Bounds (8279959 / 50000000) (165599181 / 1000000000) (Real.log (11801 / 10000)) := by
  have h := reflection_log_4171_neg
  have he : Real.log (11801 / 10000) = -Real.log (10000 / 11801) := by
    rw [show ((11801 / 10000) : ℝ) = ((10000 / 11801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4172_neg : (198572897 / 1000000000) ≤ -Real.log (8199 / 10000) ∧
    -Real.log (8199 / 10000) ≤ (99286449 / 500000000) := by
  have h := checkLog_sound (w := (1801 / 18199)) (n := 12)
    (lo := (198572897 / 1000000000)) (hi := (99286449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8199) = 1/(8199 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4172 : Bounds (-99286449 / 500000000) (-198572897 / 1000000000) (Real.log (8199 / 10000)) := by
  have h := reflection_log_4172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4173_neg : (180083 / 1000000000) ≤ -Real.log (10000000 / 10001801) ∧
    -Real.log (10000000 / 10001801) ≤ (45021 / 250000000) := by
  have h := checkLog_sound (w := (1801 / 20001801)) (n := 12)
    (lo := (180083 / 1000000000)) (hi := (45021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001801 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001801 / 10000000) = 1/(10000000 / 10001801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4173 : Bounds (180083 / 1000000000) (45021 / 250000000) (Real.log (10001801 / 10000000)) := by
  have h := reflection_log_4173_neg
  have he : Real.log (10001801 / 10000000) = -Real.log (10000000 / 10001801) := by
    rw [show ((10001801 / 10000000) : ℝ) = ((10000000 / 10001801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4174_neg : (45029 / 250000000) ≤ -Real.log (9998199 / 10000000) ∧
    -Real.log (9998199 / 10000000) ≤ (180117 / 1000000000) := by
  have h := checkLog_sound (w := (1801 / 19998199)) (n := 12)
    (lo := (45029 / 250000000)) (hi := (180117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998199) = 1/(9998199 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4174 : Bounds (-180117 / 1000000000) (-45029 / 250000000) (Real.log (9998199 / 10000000)) := by
  have h := reflection_log_4174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4175_neg : (86582201 / 1000000000) ≤ -Real.log (1000000 / 1090441) ∧
    -Real.log (1000000 / 1090441) ≤ (43291101 / 500000000) := by
  have h := checkLog_sound (w := (90441 / 2090441)) (n := 12)
    (lo := (86582201 / 1000000000)) (hi := (43291101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090441 / 1000000) = 1/(1000000 / 1090441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4175 : Bounds (86582201 / 1000000000) (43291101 / 500000000) (Real.log (1090441 / 1000000)) := by
  have h := reflection_log_4175_neg
  have he : Real.log (1090441 / 1000000) = -Real.log (1000000 / 1090441) := by
    rw [show ((1090441 / 1000000) : ℝ) = ((1000000 / 1090441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4176_neg : (23698853 / 250000000) ≤ -Real.log (909559 / 1000000) ∧
    -Real.log (909559 / 1000000) ≤ (94795413 / 1000000000) := by
  have h := checkLog_sound (w := (90441 / 1909559)) (n := 12)
    (lo := (23698853 / 250000000)) (hi := (94795413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909559) = 1/(909559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4176 : Bounds (-94795413 / 1000000000) (-23698853 / 250000000) (Real.log (909559 / 1000000)) := by
  have h := reflection_log_4176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4177_neg : (4339701 / 50000000) ≤ -Real.log (62500 / 68167) ∧
    -Real.log (62500 / 68167) ≤ (86794021 / 1000000000) := by
  have h := checkLog_sound (w := (5667 / 130667)) (n := 12)
    (lo := (4339701 / 50000000)) (hi := (86794021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68167 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68167 / 62500) = 1/(62500 / 68167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4177 : Bounds (4339701 / 50000000) (86794021 / 1000000000) (Real.log (68167 / 62500)) := by
  have h := reflection_log_4177_neg
  have he : Real.log (68167 / 62500) = -Real.log (62500 / 68167) := by
    rw [show ((68167 / 62500) : ℝ) = ((62500 / 68167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4178_neg : (95049413 / 1000000000) ≤ -Real.log (56833 / 62500) ∧
    -Real.log (56833 / 62500) ≤ (47524707 / 500000000) := by
  have h := checkLog_sound (w := (5667 / 119333)) (n := 12)
    (lo := (95049413 / 1000000000)) (hi := (47524707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56833) = 1/(56833 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4178 : Bounds (-47524707 / 500000000) (-95049413 / 1000000000) (Real.log (56833 / 62500)) := by
  have h := reflection_log_4178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4179_neg : (8255393 / 1000000000) ≤ -Real.log (3874135111 / 3906250000) ∧
    -Real.log (3874135111 / 3906250000) ≤ (4127697 / 500000000) := by
  have h := checkLog_sound (w := (32114889 / 7780385111)) (n := 12)
    (lo := (8255393 / 1000000000)) (hi := (4127697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3874135111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3874135111) = 1/(3874135111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4179 : Bounds (-4127697 / 500000000) (-8255393 / 1000000000) (Real.log (3874135111 / 3906250000)) := by
  have h := reflection_log_4179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4180_neg : (821321 / 100000000) ≤ -Real.log (991820425519 / 1000000000000) ∧
    -Real.log (991820425519 / 1000000000000) ≤ (8213211 / 1000000000) := by
  have h := checkLog_sound (w := (8179574481 / 1991820425519)) (n := 12)
    (lo := (821321 / 100000000)) (hi := (8213211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991820425519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991820425519) = 1/(991820425519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4180 : Bounds (-8213211 / 1000000000) (-821321 / 100000000) (Real.log (991820425519 / 1000000000000)) := by
  have h := reflection_log_4180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4181_neg : (181377613 / 1000000000) ≤ -Real.log (125000000000 / 149858475371) ∧
    -Real.log (125000000000 / 149858475371) ≤ (90688807 / 500000000) := by
  have h := checkLog_sound (w := (24858475371 / 274858475371)) (n := 12)
    (lo := (181377613 / 1000000000)) (hi := (90688807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149858475371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149858475371 / 125000000000) = 1/(125000000000 / 149858475371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4181 : Bounds (181377613 / 1000000000) (90688807 / 500000000) (Real.log (149858475371 / 125000000000)) := by
  have h := reflection_log_4181_neg
  have he : Real.log (149858475371 / 125000000000) = -Real.log (125000000000 / 149858475371) := by
    rw [show ((149858475371 / 125000000000) : ℝ) = ((125000000000 / 149858475371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4182_neg : (181843433 / 1000000000) ≤ -Real.log (500000000000 / 599713194799) ∧
    -Real.log (500000000000 / 599713194799) ≤ (90921717 / 500000000) := by
  have h := checkLog_sound (w := (99713194799 / 1099713194799)) (n := 12)
    (lo := (181843433 / 1000000000)) (hi := (90921717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599713194799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599713194799 / 500000000000) = 1/(500000000000 / 599713194799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4182 : Bounds (181843433 / 1000000000) (90921717 / 500000000) (Real.log (599713194799 / 500000000000)) := by
  have h := reflection_log_4182_neg
  have he : Real.log (599713194799 / 500000000000) = -Real.log (500000000000 / 599713194799) := by
    rw [show ((599713194799 / 500000000000) : ℝ) = ((500000000000 / 599713194799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4183_neg : (363965377 / 1000000000) ≤ -Real.log (500000000000 / 719512195121) ∧
    -Real.log (500000000000 / 719512195121) ≤ (181982689 / 500000000) := by
  have h := checkLog_sound (w := (219512195121 / 1219512195121)) (n := 12)
    (lo := (363965377 / 1000000000)) (hi := (181982689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719512195121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719512195121 / 500000000000) = 1/(500000000000 / 719512195121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4183 : Bounds (363965377 / 1000000000) (181982689 / 500000000) (Real.log (719512195121 / 500000000000)) := by
  have h := reflection_log_4183_neg
  have he : Real.log (719512195121 / 500000000000) = -Real.log (500000000000 / 719512195121) := by
    rw [show ((719512195121 / 500000000000) : ℝ) = ((500000000000 / 719512195121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4184_neg : (182086039 / 500000000) ≤ -Real.log (500000000000 / 719660934261) ∧
    -Real.log (500000000000 / 719660934261) ≤ (364172079 / 1000000000) := by
  have h := checkLog_sound (w := (219660934261 / 1219660934261)) (n := 12)
    (lo := (182086039 / 500000000)) (hi := (364172079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719660934261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719660934261 / 500000000000) = 1/(500000000000 / 719660934261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4184 : Bounds (182086039 / 500000000) (364172079 / 1000000000) (Real.log (719660934261 / 500000000000)) := by
  have h := reflection_log_4184_neg
  have he : Real.log (719660934261 / 500000000000) = -Real.log (500000000000 / 719660934261) := by
    rw [show ((719660934261 / 500000000000) : ℝ) = ((500000000000 / 719660934261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4185_neg : (33136783 / 200000000) ≤ -Real.log (5000 / 5901) ∧
    -Real.log (5000 / 5901) ≤ (41420979 / 250000000) := by
  have h := checkLog_sound (w := (901 / 10901)) (n := 12)
    (lo := (33136783 / 200000000)) (hi := (41420979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5901 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5901 / 5000) = 1/(5000 / 5901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4185 : Bounds (33136783 / 200000000) (41420979 / 250000000) (Real.log (5901 / 5000)) := by
  have h := reflection_log_4185_neg
  have he : Real.log (5901 / 5000) = -Real.log (5000 / 5901) := by
    rw [show ((5901 / 5000) : ℝ) = ((5000 / 5901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4186_neg : (19869487 / 100000000) ≤ -Real.log (4099 / 5000) ∧
    -Real.log (4099 / 5000) ≤ (198694871 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 9099)) (n := 12)
    (lo := (19869487 / 100000000)) (hi := (198694871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4099) = 1/(4099 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4186 : Bounds (-198694871 / 1000000000) (-19869487 / 100000000) (Real.log (4099 / 5000)) := by
  have h := reflection_log_4186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4187_neg : (180183 / 1000000000) ≤ -Real.log (5000000 / 5000901) ∧
    -Real.log (5000000 / 5000901) ≤ (22523 / 125000000) := by
  have h := checkLog_sound (w := (901 / 10000901)) (n := 12)
    (lo := (180183 / 1000000000)) (hi := (22523 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000901 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000901 / 5000000) = 1/(5000000 / 5000901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4187 : Bounds (180183 / 1000000000) (22523 / 125000000) (Real.log (5000901 / 5000000)) := by
  have h := reflection_log_4187_neg
  have he : Real.log (5000901 / 5000000) = -Real.log (5000000 / 5000901) := by
    rw [show ((5000901 / 5000000) : ℝ) = ((5000000 / 5000901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4188_neg : (22527 / 125000000) ≤ -Real.log (4999099 / 5000000) ∧
    -Real.log (4999099 / 5000000) ≤ (180217 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 9999099)) (n := 12)
    (lo := (22527 / 125000000)) (hi := (180217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999099) = 1/(4999099 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4188 : Bounds (-180217 / 1000000000) (-22527 / 125000000) (Real.log (4999099 / 5000000)) := by
  have h := reflection_log_4188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4189_neg : (8662897 / 100000000) ≤ -Real.log (250000 / 272623) ∧
    -Real.log (250000 / 272623) ≤ (86628971 / 1000000000) := by
  have h := checkLog_sound (w := (22623 / 522623)) (n := 12)
    (lo := (8662897 / 100000000)) (hi := (86628971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272623 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272623 / 250000) = 1/(250000 / 272623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4189 : Bounds (8662897 / 100000000) (86628971 / 1000000000) (Real.log (272623 / 250000)) := by
  have h := reflection_log_4189_neg
  have he : Real.log (272623 / 250000) = -Real.log (250000 / 272623) := by
    rw [show ((272623 / 250000) : ℝ) = ((250000 / 272623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4190_neg : (18970297 / 200000000) ≤ -Real.log (227377 / 250000) ∧
    -Real.log (227377 / 250000) ≤ (47425743 / 500000000) := by
  have h := checkLog_sound (w := (22623 / 477377)) (n := 12)
    (lo := (18970297 / 200000000)) (hi := (47425743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227377) = 1/(227377 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4190 : Bounds (-47425743 / 500000000) (-18970297 / 200000000) (Real.log (227377 / 250000)) := by
  have h := reflection_log_4190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4191_neg : (86840779 / 1000000000) ≤ -Real.log (1000000 / 1090723) ∧
    -Real.log (1000000 / 1090723) ≤ (4342039 / 50000000) := by
  have h := checkLog_sound (w := (90723 / 2090723)) (n := 12)
    (lo := (86840779 / 1000000000)) (hi := (4342039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090723 / 1000000) = 1/(1000000 / 1090723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4191 : Bounds (86840779 / 1000000000) (4342039 / 50000000) (Real.log (1090723 / 1000000)) := by
  have h := reflection_log_4191_neg
  have he : Real.log (1090723 / 1000000) = -Real.log (1000000 / 1090723) := by
    rw [show ((1090723 / 1000000) : ℝ) = ((1000000 / 1090723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4192_neg : (190211 / 2000000) ≤ -Real.log (909277 / 1000000) ∧
    -Real.log (909277 / 1000000) ≤ (95105501 / 1000000000) := by
  have h := checkLog_sound (w := (90723 / 1909277)) (n := 12)
    (lo := (190211 / 2000000)) (hi := (95105501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909277) = 1/(909277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4192 : Bounds (-95105501 / 1000000000) (-190211 / 2000000) (Real.log (909277 / 1000000)) := by
  have h := reflection_log_4192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4193_neg : (8264721 / 1000000000) ≤ -Real.log (991769337271 / 1000000000000) ∧
    -Real.log (991769337271 / 1000000000000) ≤ (4132361 / 500000000) := by
  have h := checkLog_sound (w := (8230662729 / 1991769337271)) (n := 12)
    (lo := (8264721 / 1000000000)) (hi := (4132361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991769337271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991769337271) = 1/(991769337271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4193 : Bounds (-4132361 / 500000000) (-8264721 / 1000000000) (Real.log (991769337271 / 1000000000000)) := by
  have h := reflection_log_4193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4194_neg : (4111257 / 500000000) ≤ -Real.log (61988199871 / 62500000000) ∧
    -Real.log (61988199871 / 62500000000) ≤ (1644503 / 200000000) := by
  have h := checkLog_sound (w := (511800129 / 124488199871)) (n := 12)
    (lo := (4111257 / 500000000)) (hi := (1644503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61988199871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61988199871) = 1/(61988199871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4194 : Bounds (-1644503 / 200000000) (-4111257 / 500000000) (Real.log (61988199871 / 62500000000)) := by
  have h := reflection_log_4194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4195_neg : (36296091 / 200000000) ≤ -Real.log (6250000000 / 7493694393) ∧
    -Real.log (6250000000 / 7493694393) ≤ (22685057 / 125000000) := by
  have h := checkLog_sound (w := (1243694393 / 13743694393)) (n := 12)
    (lo := (36296091 / 200000000)) (hi := (22685057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7493694393 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7493694393 / 6250000000) = 1/(6250000000 / 7493694393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4195 : Bounds (36296091 / 200000000) (22685057 / 125000000) (Real.log (7493694393 / 6250000000)) := by
  have h := reflection_log_4195_neg
  have he : Real.log (7493694393 / 6250000000) = -Real.log (6250000000 / 7493694393) := by
    rw [show ((7493694393 / 6250000000) : ℝ) = ((6250000000 / 7493694393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4196_neg : (181946279 / 1000000000) ≤ -Real.log (500000000000 / 599774876083) ∧
    -Real.log (500000000000 / 599774876083) ≤ (4548657 / 25000000) := by
  have h := checkLog_sound (w := (99774876083 / 1099774876083)) (n := 12)
    (lo := (181946279 / 1000000000)) (hi := (4548657 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599774876083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599774876083 / 500000000000) = 1/(500000000000 / 599774876083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4196 : Bounds (181946279 / 1000000000) (4548657 / 25000000) (Real.log (599774876083 / 500000000000)) := by
  have h := reflection_log_4196_neg
  have he : Real.log (599774876083 / 500000000000) = -Real.log (500000000000 / 599774876083) := by
    rw [show ((599774876083 / 500000000000) : ℝ) = ((500000000000 / 599774876083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4197_neg : (182086039 / 500000000) ≤ -Real.log (25000000000 / 35983046713) ∧
    -Real.log (25000000000 / 35983046713) ≤ (364172079 / 1000000000) := by
  have h := checkLog_sound (w := (10983046713 / 60983046713)) (n := 12)
    (lo := (182086039 / 500000000)) (hi := (364172079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35983046713 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35983046713 / 25000000000) = 1/(25000000000 / 35983046713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4197 : Bounds (182086039 / 500000000) (364172079 / 1000000000) (Real.log (35983046713 / 25000000000)) := by
  have h := reflection_log_4197_neg
  have he : Real.log (35983046713 / 25000000000) = -Real.log (25000000000 / 35983046713) := by
    rw [show ((35983046713 / 25000000000) : ℝ) = ((25000000000 / 35983046713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4198_neg : (182189393 / 500000000) ≤ -Real.log (250000000000 / 359904854843) ∧
    -Real.log (250000000000 / 359904854843) ≤ (364378787 / 1000000000) := by
  have h := checkLog_sound (w := (109904854843 / 609904854843)) (n := 12)
    (lo := (182189393 / 500000000)) (hi := (364378787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359904854843 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359904854843 / 250000000000) = 1/(250000000000 / 359904854843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4198 : Bounds (182189393 / 500000000) (364378787 / 1000000000) (Real.log (359904854843 / 250000000000)) := by
  have h := reflection_log_4198_neg
  have he : Real.log (359904854843 / 250000000000) = -Real.log (250000000000 / 359904854843) := by
    rw [show ((359904854843 / 250000000000) : ℝ) = ((250000000000 / 359904854843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4199_neg : (165768643 / 1000000000) ≤ -Real.log (10000 / 11803) ∧
    -Real.log (10000 / 11803) ≤ (41442161 / 250000000) := by
  have h := checkLog_sound (w := (1803 / 21803)) (n := 12)
    (lo := (165768643 / 1000000000)) (hi := (41442161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 10000) = 1/(10000 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4199 : Bounds (165768643 / 1000000000) (41442161 / 250000000) (Real.log (11803 / 10000)) := by
  have h := reflection_log_4199_neg
  have he : Real.log (11803 / 10000) = -Real.log (10000 / 11803) := by
    rw [show ((11803 / 10000) : ℝ) = ((10000 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4200_neg : (198816859 / 1000000000) ≤ -Real.log (8197 / 10000) ∧
    -Real.log (8197 / 10000) ≤ (9940843 / 50000000) := by
  have h := checkLog_sound (w := (1803 / 18197)) (n := 12)
    (lo := (198816859 / 1000000000)) (hi := (9940843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8197) = 1/(8197 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4200 : Bounds (-9940843 / 50000000) (-198816859 / 1000000000) (Real.log (8197 / 10000)) := by
  have h := reflection_log_4200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4201_neg : (180283 / 1000000000) ≤ -Real.log (10000000 / 10001803) ∧
    -Real.log (10000000 / 10001803) ≤ (45071 / 250000000) := by
  have h := checkLog_sound (w := (1803 / 20001803)) (n := 12)
    (lo := (180283 / 1000000000)) (hi := (45071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001803 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001803 / 10000000) = 1/(10000000 / 10001803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4201 : Bounds (180283 / 1000000000) (45071 / 250000000) (Real.log (10001803 / 10000000)) := by
  have h := reflection_log_4201_neg
  have he : Real.log (10001803 / 10000000) = -Real.log (10000000 / 10001803) := by
    rw [show ((10001803 / 10000000) : ℝ) = ((10000000 / 10001803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4202_neg : (45079 / 250000000) ≤ -Real.log (9998197 / 10000000) ∧
    -Real.log (9998197 / 10000000) ≤ (180317 / 1000000000) := by
  have h := checkLog_sound (w := (1803 / 19998197)) (n := 12)
    (lo := (45079 / 250000000)) (hi := (180317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998197) = 1/(9998197 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4202 : Bounds (-180317 / 1000000000) (-45079 / 250000000) (Real.log (9998197 / 10000000)) := by
  have h := reflection_log_4202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4203_neg : (86675737 / 1000000000) ≤ -Real.log (1000000 / 1090543) ∧
    -Real.log (1000000 / 1090543) ≤ (43337869 / 500000000) := by
  have h := checkLog_sound (w := (90543 / 2090543)) (n := 12)
    (lo := (86675737 / 1000000000)) (hi := (43337869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090543 / 1000000) = 1/(1000000 / 1090543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4203 : Bounds (86675737 / 1000000000) (43337869 / 500000000) (Real.log (1090543 / 1000000)) := by
  have h := reflection_log_4203_neg
  have he : Real.log (1090543 / 1000000) = -Real.log (1000000 / 1090543) := by
    rw [show ((1090543 / 1000000) : ℝ) = ((1000000 / 1090543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4204_neg : (2372689 / 25000000) ≤ -Real.log (909457 / 1000000) ∧
    -Real.log (909457 / 1000000) ≤ (94907561 / 1000000000) := by
  have h := checkLog_sound (w := (90543 / 1909457)) (n := 12)
    (lo := (2372689 / 25000000)) (hi := (94907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909457) = 1/(909457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4204 : Bounds (-94907561 / 1000000000) (-2372689 / 25000000) (Real.log (909457 / 1000000)) := by
  have h := reflection_log_4204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4205_neg : (17377507 / 200000000) ≤ -Real.log (500000 / 545387) ∧
    -Real.log (500000 / 545387) ≤ (5430471 / 62500000) := by
  have h := checkLog_sound (w := (45387 / 1045387)) (n := 12)
    (lo := (17377507 / 200000000)) (hi := (5430471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545387 / 500000) = 1/(500000 / 545387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4205 : Bounds (17377507 / 200000000) (5430471 / 62500000) (Real.log (545387 / 500000)) := by
  have h := reflection_log_4205_neg
  have he : Real.log (545387 / 500000) = -Real.log (500000 / 545387) := by
    rw [show ((545387 / 500000) : ℝ) = ((500000 / 545387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4206_neg : (9516159 / 100000000) ≤ -Real.log (454613 / 500000) ∧
    -Real.log (454613 / 500000) ≤ (95161591 / 1000000000) := by
  have h := checkLog_sound (w := (45387 / 954613)) (n := 12)
    (lo := (9516159 / 100000000)) (hi := (95161591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454613) = 1/(454613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4206 : Bounds (-95161591 / 1000000000) (-9516159 / 100000000) (Real.log (454613 / 500000)) := by
  have h := reflection_log_4206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4207_neg : (4137027 / 500000000) ≤ -Real.log (247940020231 / 250000000000) ∧
    -Real.log (247940020231 / 250000000000) ≤ (1654811 / 200000000) := by
  have h := checkLog_sound (w := (2059979769 / 497940020231)) (n := 12)
    (lo := (4137027 / 500000000)) (hi := (1654811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247940020231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247940020231) = 1/(247940020231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4207 : Bounds (-1654811 / 200000000) (-4137027 / 500000000) (Real.log (247940020231 / 250000000000)) := by
  have h := reflection_log_4207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4208_neg : (8231823 / 1000000000) ≤ -Real.log (991801965151 / 1000000000000) ∧
    -Real.log (991801965151 / 1000000000000) ≤ (514489 / 62500000) := by
  have h := checkLog_sound (w := (8198034849 / 1991801965151)) (n := 12)
    (lo := (8231823 / 1000000000)) (hi := (514489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991801965151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991801965151) = 1/(991801965151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4208 : Bounds (-514489 / 62500000) (-8231823 / 1000000000) (Real.log (991801965151 / 1000000000000)) := by
  have h := reflection_log_4208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4209_neg : (90791649 / 500000000) ≤ -Real.log (62500000000 / 74944651039) ∧
    -Real.log (62500000000 / 74944651039) ≤ (181583299 / 1000000000) := by
  have h := checkLog_sound (w := (12444651039 / 137444651039)) (n := 12)
    (lo := (90791649 / 500000000)) (hi := (181583299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74944651039 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74944651039 / 62500000000) = 1/(62500000000 / 74944651039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4209 : Bounds (90791649 / 500000000) (181583299 / 1000000000) (Real.log (74944651039 / 62500000000)) := by
  have h := reflection_log_4209_neg
  have he : Real.log (74944651039 / 62500000000) = -Real.log (62500000000 / 74944651039) := by
    rw [show ((74944651039 / 62500000000) : ℝ) = ((62500000000 / 74944651039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4210_neg : (91024563 / 500000000) ≤ -Real.log (500000000000 / 599836564287) ∧
    -Real.log (500000000000 / 599836564287) ≤ (182049127 / 1000000000) := by
  have h := checkLog_sound (w := (99836564287 / 1099836564287)) (n := 12)
    (lo := (91024563 / 500000000)) (hi := (182049127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599836564287 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599836564287 / 500000000000) = 1/(500000000000 / 599836564287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4210 : Bounds (91024563 / 500000000) (182049127 / 1000000000) (Real.log (599836564287 / 500000000000)) := by
  have h := reflection_log_4210_neg
  have he : Real.log (599836564287 / 500000000000) = -Real.log (500000000000 / 599836564287) := by
    rw [show ((599836564287 / 500000000000) : ℝ) = ((500000000000 / 599836564287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4211_neg : (182189393 / 500000000) ≤ -Real.log (100000000000 / 143961941937) ∧
    -Real.log (100000000000 / 143961941937) ≤ (364378787 / 1000000000) := by
  have h := checkLog_sound (w := (43961941937 / 243961941937)) (n := 12)
    (lo := (182189393 / 500000000)) (hi := (364378787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143961941937 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143961941937 / 100000000000) = 1/(100000000000 / 143961941937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4211 : Bounds (182189393 / 500000000) (364378787 / 1000000000) (Real.log (143961941937 / 100000000000)) := by
  have h := reflection_log_4211_neg
  have he : Real.log (143961941937 / 100000000000) = -Real.log (100000000000 / 143961941937) := by
    rw [show ((143961941937 / 100000000000) : ℝ) = ((100000000000 / 143961941937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4212_neg : (182292751 / 500000000) ≤ -Real.log (500000000000 / 719958521411) ∧
    -Real.log (500000000000 / 719958521411) ≤ (364585503 / 1000000000) := by
  have h := checkLog_sound (w := (219958521411 / 1219958521411)) (n := 12)
    (lo := (182292751 / 500000000)) (hi := (364585503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719958521411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719958521411 / 500000000000) = 1/(500000000000 / 719958521411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4212 : Bounds (182292751 / 500000000) (364585503 / 1000000000) (Real.log (719958521411 / 500000000000)) := by
  have h := reflection_log_4212_neg
  have he : Real.log (719958521411 / 500000000000) = -Real.log (500000000000 / 719958521411) := by
    rw [show ((719958521411 / 500000000000) : ℝ) = ((500000000000 / 719958521411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4213_neg : (41463341 / 250000000) ≤ -Real.log (2500 / 2951) ∧
    -Real.log (2500 / 2951) ≤ (33170673 / 200000000) := by
  have h := checkLog_sound (w := (451 / 5451)) (n := 12)
    (lo := (41463341 / 250000000)) (hi := (33170673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2951 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2951 / 2500) = 1/(2500 / 2951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4213 : Bounds (41463341 / 250000000) (33170673 / 200000000) (Real.log (2951 / 2500)) := by
  have h := reflection_log_4213_neg
  have he : Real.log (2951 / 2500) = -Real.log (2500 / 2951) := by
    rw [show ((2951 / 2500) : ℝ) = ((2500 / 2951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4214_neg : (99469431 / 500000000) ≤ -Real.log (2049 / 2500) ∧
    -Real.log (2049 / 2500) ≤ (198938863 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 4549)) (n := 12)
    (lo := (99469431 / 500000000)) (hi := (198938863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2049) = 1/(2049 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4214 : Bounds (-198938863 / 1000000000) (-99469431 / 500000000) (Real.log (2049 / 2500)) := by
  have h := reflection_log_4214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4215_neg : (180383 / 1000000000) ≤ -Real.log (2500000 / 2500451) ∧
    -Real.log (2500000 / 2500451) ≤ (5637 / 31250000) := by
  have h := checkLog_sound (w := (451 / 5000451)) (n := 12)
    (lo := (180383 / 1000000000)) (hi := (5637 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500451 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500451 / 2500000) = 1/(2500000 / 2500451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4215 : Bounds (180383 / 1000000000) (5637 / 31250000) (Real.log (2500451 / 2500000)) := by
  have h := reflection_log_4215_neg
  have he : Real.log (2500451 / 2500000) = -Real.log (2500000 / 2500451) := by
    rw [show ((2500451 / 2500000) : ℝ) = ((2500000 / 2500451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4216_neg : (2819 / 15625000) ≤ -Real.log (2499549 / 2500000) ∧
    -Real.log (2499549 / 2500000) ≤ (180417 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 4999549)) (n := 12)
    (lo := (2819 / 15625000)) (hi := (180417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499549) = 1/(2499549 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4216 : Bounds (-180417 / 1000000000) (-2819 / 15625000) (Real.log (2499549 / 2500000)) := by
  have h := reflection_log_4216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4217_neg : (17344317 / 200000000) ≤ -Real.log (1000000 / 1090593) ∧
    -Real.log (1000000 / 1090593) ≤ (43360793 / 500000000) := by
  have h := checkLog_sound (w := (90593 / 2090593)) (n := 12)
    (lo := (17344317 / 200000000)) (hi := (43360793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090593 / 1000000) = 1/(1000000 / 1090593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4217 : Bounds (17344317 / 200000000) (43360793 / 500000000) (Real.log (1090593 / 1000000)) := by
  have h := reflection_log_4217_neg
  have he : Real.log (1090593 / 1000000) = -Real.log (1000000 / 1090593) := by
    rw [show ((1090593 / 1000000) : ℝ) = ((1000000 / 1090593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4218_neg : (4748127 / 50000000) ≤ -Real.log (909407 / 1000000) ∧
    -Real.log (909407 / 1000000) ≤ (94962541 / 1000000000) := by
  have h := checkLog_sound (w := (90593 / 1909407)) (n := 12)
    (lo := (4748127 / 50000000)) (hi := (94962541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909407) = 1/(909407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4218 : Bounds (-94962541 / 1000000000) (-4748127 / 50000000) (Real.log (909407 / 1000000)) := by
  have h := reflection_log_4218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4219_neg : (8693429 / 100000000) ≤ -Real.log (40000 / 43633) ∧
    -Real.log (40000 / 43633) ≤ (86934291 / 1000000000) := by
  have h := checkLog_sound (w := (3633 / 83633)) (n := 12)
    (lo := (8693429 / 100000000)) (hi := (86934291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43633 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43633 / 40000) = 1/(40000 / 43633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4219 : Bounds (8693429 / 100000000) (86934291 / 1000000000) (Real.log (43633 / 40000)) := by
  have h := reflection_log_4219_neg
  have he : Real.log (43633 / 40000) = -Real.log (40000 / 43633) := by
    rw [show ((43633 / 40000) : ℝ) = ((40000 / 43633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4220_neg : (23804421 / 250000000) ≤ -Real.log (36367 / 40000) ∧
    -Real.log (36367 / 40000) ≤ (19043537 / 200000000) := by
  have h := checkLog_sound (w := (3633 / 76367)) (n := 12)
    (lo := (23804421 / 250000000)) (hi := (19043537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36367) = 1/(36367 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4220 : Bounds (-19043537 / 200000000) (-23804421 / 250000000) (Real.log (36367 / 40000)) := by
  have h := reflection_log_4220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4221_neg : (8283393 / 1000000000) ≤ -Real.log (1586801311 / 1600000000) ∧
    -Real.log (1586801311 / 1600000000) ≤ (4141697 / 500000000) := by
  have h := checkLog_sound (w := (13198689 / 3186801311)) (n := 12)
    (lo := (8283393 / 1000000000)) (hi := (4141697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586801311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586801311) = 1/(1586801311 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4221 : Bounds (-4141697 / 500000000) (-8283393 / 1000000000) (Real.log (1586801311 / 1600000000)) := by
  have h := reflection_log_4221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4222_neg : (1648191 / 200000000) ≤ -Real.log (991792908351 / 1000000000000) ∧
    -Real.log (991792908351 / 1000000000000) ≤ (2060239 / 250000000) := by
  have h := checkLog_sound (w := (8207091649 / 1991792908351)) (n := 12)
    (lo := (1648191 / 200000000)) (hi := (2060239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991792908351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991792908351) = 1/(991792908351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4222 : Bounds (-2060239 / 250000000) (-1648191 / 200000000) (Real.log (991792908351 / 1000000000000)) := by
  have h := reflection_log_4222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4223_neg : (1453473 / 8000000) ≤ -Real.log (250000000000 / 299808831469) ∧
    -Real.log (250000000000 / 299808831469) ≤ (90842063 / 500000000) := by
  have h := checkLog_sound (w := (49808831469 / 549808831469)) (n := 12)
    (lo := (1453473 / 8000000)) (hi := (90842063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299808831469 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299808831469 / 250000000000) = 1/(250000000000 / 299808831469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4223 : Bounds (1453473 / 8000000) (90842063 / 500000000) (Real.log (299808831469 / 250000000000)) := by
  have h := reflection_log_4223_neg
  have he : Real.log (299808831469 / 250000000000) = -Real.log (250000000000 / 299808831469) := by
    rw [show ((299808831469 / 250000000000) : ℝ) = ((250000000000 / 299808831469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0066 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4224_neg : (91075987 / 500000000) ≤ -Real.log (125000000000 / 149974564853) ∧
    -Real.log (125000000000 / 149974564853) ≤ (7286079 / 40000000) := by
  have h := checkLog_sound (w := (24974564853 / 274974564853)) (n := 12)
    (lo := (91075987 / 500000000)) (hi := (7286079 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149974564853 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149974564853 / 125000000000) = 1/(125000000000 / 149974564853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4224 : Bounds (91075987 / 500000000) (7286079 / 40000000) (Real.log (149974564853 / 125000000000)) := by
  have h := reflection_log_4224_neg
  have he : Real.log (149974564853 / 125000000000) = -Real.log (125000000000 / 149974564853) := by
    rw [show ((149974564853 / 125000000000) : ℝ) = ((125000000000 / 149974564853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4225_neg : (182292751 / 500000000) ≤ -Real.log (50000000000 / 71995852141) ∧
    -Real.log (50000000000 / 71995852141) ≤ (364585503 / 1000000000) := by
  have h := checkLog_sound (w := (21995852141 / 121995852141)) (n := 12)
    (lo := (182292751 / 500000000)) (hi := (364585503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71995852141 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71995852141 / 50000000000) = 1/(50000000000 / 71995852141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4225 : Bounds (182292751 / 500000000) (364585503 / 1000000000) (Real.log (71995852141 / 50000000000)) := by
  have h := reflection_log_4225_neg
  have he : Real.log (71995852141 / 50000000000) = -Real.log (50000000000 / 71995852141) := by
    rw [show ((71995852141 / 50000000000) : ℝ) = ((50000000000 / 71995852141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4226_neg : (182396113 / 500000000) ≤ -Real.log (500000000000 / 720107369449) ∧
    -Real.log (500000000000 / 720107369449) ≤ (364792227 / 1000000000) := by
  have h := checkLog_sound (w := (220107369449 / 1220107369449)) (n := 12)
    (lo := (182396113 / 500000000)) (hi := (364792227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720107369449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720107369449 / 500000000000) = 1/(500000000000 / 720107369449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4226 : Bounds (182396113 / 500000000) (364792227 / 1000000000) (Real.log (720107369449 / 500000000000)) := by
  have h := reflection_log_4226_neg
  have he : Real.log (720107369449 / 500000000000) = -Real.log (500000000000 / 720107369449) := by
    rw [show ((720107369449 / 500000000000) : ℝ) = ((500000000000 / 720107369449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4227_neg : (165938077 / 1000000000) ≤ -Real.log (2000 / 2361) ∧
    -Real.log (2000 / 2361) ≤ (82969039 / 500000000) := by
  have h := checkLog_sound (w := (361 / 4361)) (n := 12)
    (lo := (165938077 / 1000000000)) (hi := (82969039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2361 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2361 / 2000) = 1/(2000 / 2361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4227 : Bounds (165938077 / 1000000000) (82969039 / 500000000) (Real.log (2361 / 2000)) := by
  have h := reflection_log_4227_neg
  have he : Real.log (2361 / 2000) = -Real.log (2000 / 2361) := by
    rw [show ((2361 / 2000) : ℝ) = ((2000 / 2361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4228_neg : (2488261 / 12500000) ≤ -Real.log (1639 / 2000) ∧
    -Real.log (1639 / 2000) ≤ (199060881 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 3639)) (n := 12)
    (lo := (2488261 / 12500000)) (hi := (199060881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1639) = 1/(1639 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4228 : Bounds (-199060881 / 1000000000) (-2488261 / 12500000) (Real.log (1639 / 2000)) := by
  have h := reflection_log_4228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4229_neg : (180483 / 1000000000) ≤ -Real.log (2000000 / 2000361) ∧
    -Real.log (2000000 / 2000361) ≤ (45121 / 250000000) := by
  have h := checkLog_sound (w := (361 / 4000361)) (n := 12)
    (lo := (180483 / 1000000000)) (hi := (45121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000361 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000361 / 2000000) = 1/(2000000 / 2000361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4229 : Bounds (180483 / 1000000000) (45121 / 250000000) (Real.log (2000361 / 2000000)) := by
  have h := reflection_log_4229_neg
  have he : Real.log (2000361 / 2000000) = -Real.log (2000000 / 2000361) := by
    rw [show ((2000361 / 2000000) : ℝ) = ((2000000 / 2000361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4230_neg : (45129 / 250000000) ≤ -Real.log (1999639 / 2000000) ∧
    -Real.log (1999639 / 2000000) ≤ (180517 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 3999639)) (n := 12)
    (lo := (45129 / 250000000)) (hi := (180517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999639) = 1/(1999639 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4230 : Bounds (-180517 / 1000000000) (-45129 / 250000000) (Real.log (1999639 / 2000000)) := by
  have h := reflection_log_4230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4231_neg : (86768347 / 1000000000) ≤ -Real.log (250000 / 272661) ∧
    -Real.log (250000 / 272661) ≤ (21692087 / 250000000) := by
  have h := checkLog_sound (w := (22661 / 522661)) (n := 12)
    (lo := (86768347 / 1000000000)) (hi := (21692087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272661 / 250000) = 1/(250000 / 272661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4231 : Bounds (86768347 / 1000000000) (21692087 / 250000000) (Real.log (272661 / 250000)) := by
  have h := reflection_log_4231_neg
  have he : Real.log (272661 / 250000) = -Real.log (250000 / 272661) := by
    rw [show ((272661 / 250000) : ℝ) = ((250000 / 272661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4232_neg : (47509311 / 500000000) ≤ -Real.log (227339 / 250000) ∧
    -Real.log (227339 / 250000) ≤ (95018623 / 1000000000) := by
  have h := checkLog_sound (w := (22661 / 477339)) (n := 12)
    (lo := (47509311 / 500000000)) (hi := (95018623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227339) = 1/(227339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4232 : Bounds (-95018623 / 1000000000) (-47509311 / 500000000) (Real.log (227339 / 250000)) := by
  have h := reflection_log_4232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4233_neg : (86981043 / 1000000000) ≤ -Real.log (250000 / 272719) ∧
    -Real.log (250000 / 272719) ≤ (21745261 / 250000000) := by
  have h := checkLog_sound (w := (22719 / 522719)) (n := 12)
    (lo := (86981043 / 1000000000)) (hi := (21745261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272719 / 250000) = 1/(250000 / 272719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4233 : Bounds (86981043 / 1000000000) (21745261 / 250000000) (Real.log (272719 / 250000)) := by
  have h := reflection_log_4233_neg
  have he : Real.log (272719 / 250000) = -Real.log (250000 / 272719) := by
    rw [show ((272719 / 250000) : ℝ) = ((250000 / 272719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4234_neg : (4763689 / 50000000) ≤ -Real.log (227281 / 250000) ∧
    -Real.log (227281 / 250000) ≤ (95273781 / 1000000000) := by
  have h := checkLog_sound (w := (22719 / 477281)) (n := 12)
    (lo := (4763689 / 50000000)) (hi := (95273781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227281) = 1/(227281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4234 : Bounds (-95273781 / 1000000000) (-4763689 / 50000000) (Real.log (227281 / 250000)) := by
  have h := reflection_log_4234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4235_neg : (8292737 / 1000000000) ≤ -Real.log (61983847039 / 62500000000) ∧
    -Real.log (61983847039 / 62500000000) ≤ (4146369 / 500000000) := by
  have h := checkLog_sound (w := (516152961 / 124483847039)) (n := 12)
    (lo := (8292737 / 1000000000)) (hi := (4146369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61983847039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61983847039) = 1/(61983847039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4235 : Bounds (-4146369 / 500000000) (-8292737 / 1000000000) (Real.log (61983847039 / 62500000000)) := by
  have h := reflection_log_4235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4236_neg : (4125137 / 500000000) ≤ -Real.log (61986479079 / 62500000000) ∧
    -Real.log (61986479079 / 62500000000) ≤ (330011 / 40000000) := by
  have h := checkLog_sound (w := (513520921 / 124486479079)) (n := 12)
    (lo := (4125137 / 500000000)) (hi := (330011 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61986479079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61986479079) = 1/(61986479079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4236 : Bounds (-330011 / 40000000) (-4125137 / 500000000) (Real.log (61986479079 / 62500000000)) := by
  have h := reflection_log_4236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4237_neg : (181786969 / 1000000000) ≤ -Real.log (250000000000 / 299839666753) ∧
    -Real.log (250000000000 / 299839666753) ≤ (18178697 / 100000000) := by
  have h := checkLog_sound (w := (49839666753 / 549839666753)) (n := 12)
    (lo := (181786969 / 1000000000)) (hi := (18178697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299839666753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299839666753 / 250000000000) = 1/(250000000000 / 299839666753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4237 : Bounds (181786969 / 1000000000) (18178697 / 100000000) (Real.log (299839666753 / 250000000000)) := by
  have h := reflection_log_4237_neg
  have he : Real.log (299839666753 / 250000000000) = -Real.log (250000000000 / 299839666753) := by
    rw [show ((299839666753 / 250000000000) : ℝ) = ((250000000000 / 299839666753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4238_neg : (182254823 / 1000000000) ≤ -Real.log (250000000000 / 299979980729) ∧
    -Real.log (250000000000 / 299979980729) ≤ (22781853 / 125000000) := by
  have h := checkLog_sound (w := (49979980729 / 549979980729)) (n := 12)
    (lo := (182254823 / 1000000000)) (hi := (22781853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299979980729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299979980729 / 250000000000) = 1/(250000000000 / 299979980729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4238 : Bounds (182254823 / 1000000000) (22781853 / 125000000) (Real.log (299979980729 / 250000000000)) := by
  have h := reflection_log_4238_neg
  have he : Real.log (299979980729 / 250000000000) = -Real.log (250000000000 / 299979980729) := by
    rw [show ((299979980729 / 250000000000) : ℝ) = ((250000000000 / 299979980729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4239_neg : (182396113 / 500000000) ≤ -Real.log (62500000000 / 90013421181) ∧
    -Real.log (62500000000 / 90013421181) ≤ (364792227 / 1000000000) := by
  have h := checkLog_sound (w := (27513421181 / 152513421181)) (n := 12)
    (lo := (182396113 / 500000000)) (hi := (364792227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90013421181 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90013421181 / 62500000000) = 1/(62500000000 / 90013421181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4239 : Bounds (182396113 / 500000000) (364792227 / 1000000000) (Real.log (90013421181 / 62500000000)) := by
  have h := reflection_log_4239_neg
  have he : Real.log (90013421181 / 62500000000) = -Real.log (62500000000 / 90013421181) := by
    rw [show ((90013421181 / 62500000000) : ℝ) = ((62500000000 / 90013421181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4240_neg : (182499479 / 500000000) ≤ -Real.log (250000000000 / 360128126907) ∧
    -Real.log (250000000000 / 360128126907) ≤ (364998959 / 1000000000) := by
  have h := checkLog_sound (w := (110128126907 / 610128126907)) (n := 12)
    (lo := (182499479 / 500000000)) (hi := (364998959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360128126907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360128126907 / 250000000000) = 1/(250000000000 / 360128126907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4240 : Bounds (182499479 / 500000000) (364998959 / 1000000000) (Real.log (360128126907 / 250000000000)) := by
  have h := reflection_log_4240_neg
  have he : Real.log (360128126907 / 250000000000) = -Real.log (250000000000 / 360128126907) := by
    rw [show ((360128126907 / 250000000000) : ℝ) = ((250000000000 / 360128126907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4241_neg : (166022783 / 1000000000) ≤ -Real.log (5000 / 5903) ∧
    -Real.log (5000 / 5903) ≤ (1297053 / 7812500) := by
  have h := checkLog_sound (w := (903 / 10903)) (n := 12)
    (lo := (166022783 / 1000000000)) (hi := (1297053 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5903 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5903 / 5000) = 1/(5000 / 5903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4241 : Bounds (166022783 / 1000000000) (1297053 / 7812500) (Real.log (5903 / 5000)) := by
  have h := reflection_log_4241_neg
  have he : Real.log (5903 / 5000) = -Real.log (5000 / 5903) := by
    rw [show ((5903 / 5000) : ℝ) = ((5000 / 5903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4242_neg : (199182913 / 1000000000) ≤ -Real.log (4097 / 5000) ∧
    -Real.log (4097 / 5000) ≤ (99591457 / 500000000) := by
  have h := checkLog_sound (w := (903 / 9097)) (n := 12)
    (lo := (199182913 / 1000000000)) (hi := (99591457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4097) = 1/(4097 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4242 : Bounds (-99591457 / 500000000) (-199182913 / 1000000000) (Real.log (4097 / 5000)) := by
  have h := reflection_log_4242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4243_neg : (180583 / 1000000000) ≤ -Real.log (5000000 / 5000903) ∧
    -Real.log (5000000 / 5000903) ≤ (22573 / 125000000) := by
  have h := checkLog_sound (w := (903 / 10000903)) (n := 12)
    (lo := (180583 / 1000000000)) (hi := (22573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000903 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000903 / 5000000) = 1/(5000000 / 5000903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4243 : Bounds (180583 / 1000000000) (22573 / 125000000) (Real.log (5000903 / 5000000)) := by
  have h := reflection_log_4243_neg
  have he : Real.log (5000903 / 5000000) = -Real.log (5000000 / 5000903) := by
    rw [show ((5000903 / 5000000) : ℝ) = ((5000000 / 5000903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4244_neg : (22577 / 125000000) ≤ -Real.log (4999097 / 5000000) ∧
    -Real.log (4999097 / 5000000) ≤ (180617 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 9999097)) (n := 12)
    (lo := (22577 / 125000000)) (hi := (180617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999097) = 1/(4999097 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4244 : Bounds (-180617 / 1000000000) (-22577 / 125000000) (Real.log (4999097 / 5000000)) := by
  have h := reflection_log_4244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4245_neg : (86815107 / 1000000000) ≤ -Real.log (200000 / 218139) ∧
    -Real.log (200000 / 218139) ≤ (21703777 / 250000000) := by
  have h := checkLog_sound (w := (18139 / 418139)) (n := 12)
    (lo := (86815107 / 1000000000)) (hi := (21703777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218139 / 200000) = 1/(200000 / 218139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4245 : Bounds (86815107 / 1000000000) (21703777 / 250000000) (Real.log (218139 / 200000)) := by
  have h := reflection_log_4245_neg
  have he : Real.log (218139 / 200000) = -Real.log (200000 / 218139) := by
    rw [show ((218139 / 200000) : ℝ) = ((200000 / 218139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4246_neg : (95074707 / 1000000000) ≤ -Real.log (181861 / 200000) ∧
    -Real.log (181861 / 200000) ≤ (23768677 / 250000000) := by
  have h := checkLog_sound (w := (18139 / 381861)) (n := 12)
    (lo := (95074707 / 1000000000)) (hi := (23768677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181861) = 1/(181861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4246 : Bounds (-23768677 / 250000000) (-95074707 / 1000000000) (Real.log (181861 / 200000)) := by
  have h := reflection_log_4246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4247_neg : (87027793 / 1000000000) ≤ -Real.log (1000000 / 1090927) ∧
    -Real.log (1000000 / 1090927) ≤ (43513897 / 500000000) := by
  have h := checkLog_sound (w := (90927 / 2090927)) (n := 12)
    (lo := (87027793 / 1000000000)) (hi := (43513897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090927 / 1000000) = 1/(1000000 / 1090927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4247 : Bounds (87027793 / 1000000000) (43513897 / 500000000) (Real.log (1090927 / 1000000)) := by
  have h := reflection_log_4247_neg
  have he : Real.log (1090927 / 1000000) = -Real.log (1000000 / 1090927) := by
    rw [show ((1090927 / 1000000) : ℝ) = ((1000000 / 1090927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4248_neg : (95329879 / 1000000000) ≤ -Real.log (909073 / 1000000) ∧
    -Real.log (909073 / 1000000) ≤ (2383247 / 25000000) := by
  have h := checkLog_sound (w := (90927 / 1909073)) (n := 12)
    (lo := (95329879 / 1000000000)) (hi := (2383247 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909073) = 1/(909073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4248 : Bounds (-2383247 / 25000000) (-95329879 / 1000000000) (Real.log (909073 / 1000000)) := by
  have h := reflection_log_4248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4249_neg : (4151043 / 500000000) ≤ -Real.log (991732280671 / 1000000000000) ∧
    -Real.log (991732280671 / 1000000000000) ≤ (8302087 / 1000000000) := by
  have h := checkLog_sound (w := (8267719329 / 1991732280671)) (n := 12)
    (lo := (4151043 / 500000000)) (hi := (8302087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991732280671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991732280671) = 1/(991732280671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4249 : Bounds (-8302087 / 1000000000) (-4151043 / 500000000) (Real.log (991732280671 / 1000000000000)) := by
  have h := reflection_log_4249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4250_neg : (8259599 / 1000000000) ≤ -Real.log (39670976679 / 40000000000) ∧
    -Real.log (39670976679 / 40000000000) ≤ (20649 / 2500000) := by
  have h := checkLog_sound (w := (329023321 / 79670976679)) (n := 12)
    (lo := (8259599 / 1000000000)) (hi := (20649 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39670976679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39670976679) = 1/(39670976679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4250 : Bounds (-20649 / 2500000) (-8259599 / 1000000000) (Real.log (39670976679 / 40000000000)) := by
  have h := reflection_log_4250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4251_neg : (36377963 / 200000000) ≤ -Real.log (500000000000 / 599741010991) ∧
    -Real.log (500000000000 / 599741010991) ≤ (22736227 / 125000000) := by
  have h := checkLog_sound (w := (99741010991 / 1099741010991)) (n := 12)
    (lo := (36377963 / 200000000)) (hi := (22736227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599741010991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599741010991 / 500000000000) = 1/(500000000000 / 599741010991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4251 : Bounds (36377963 / 200000000) (22736227 / 125000000) (Real.log (599741010991 / 500000000000)) := by
  have h := reflection_log_4251_neg
  have he : Real.log (599741010991 / 500000000000) = -Real.log (500000000000 / 599741010991) := by
    rw [show ((599741010991 / 500000000000) : ℝ) = ((500000000000 / 599741010991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4252_neg : (182357673 / 1000000000) ≤ -Real.log (500000000000 / 600021670427) ∧
    -Real.log (500000000000 / 600021670427) ≤ (91178837 / 500000000) := by
  have h := checkLog_sound (w := (100021670427 / 1100021670427)) (n := 12)
    (lo := (182357673 / 1000000000)) (hi := (91178837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600021670427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600021670427 / 500000000000) = 1/(500000000000 / 600021670427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4252 : Bounds (182357673 / 1000000000) (91178837 / 500000000) (Real.log (600021670427 / 500000000000)) := by
  have h := reflection_log_4252_neg
  have he : Real.log (600021670427 / 500000000000) = -Real.log (500000000000 / 600021670427) := by
    rw [show ((600021670427 / 500000000000) : ℝ) = ((500000000000 / 600021670427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4253_neg : (182499479 / 500000000) ≤ -Real.log (500000000000 / 720256253813) ∧
    -Real.log (500000000000 / 720256253813) ≤ (364998959 / 1000000000) := by
  have h := checkLog_sound (w := (220256253813 / 1220256253813)) (n := 12)
    (lo := (182499479 / 500000000)) (hi := (364998959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720256253813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720256253813 / 500000000000) = 1/(500000000000 / 720256253813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4253 : Bounds (182499479 / 500000000) (364998959 / 1000000000) (Real.log (720256253813 / 500000000000)) := by
  have h := reflection_log_4253_neg
  have he : Real.log (720256253813 / 500000000000) = -Real.log (500000000000 / 720256253813) := by
    rw [show ((720256253813 / 500000000000) : ℝ) = ((500000000000 / 720256253813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4254_neg : (365205697 / 1000000000) ≤ -Real.log (250000000000 / 360202587259) ∧
    -Real.log (250000000000 / 360202587259) ≤ (182602849 / 500000000) := by
  have h := checkLog_sound (w := (110202587259 / 610202587259)) (n := 12)
    (lo := (365205697 / 1000000000)) (hi := (182602849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360202587259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360202587259 / 250000000000) = 1/(250000000000 / 360202587259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4254 : Bounds (365205697 / 1000000000) (182602849 / 500000000) (Real.log (360202587259 / 250000000000)) := by
  have h := reflection_log_4254_neg
  have he : Real.log (360202587259 / 250000000000) = -Real.log (250000000000 / 360202587259) := by
    rw [show ((360202587259 / 250000000000) : ℝ) = ((250000000000 / 360202587259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4255_neg : (83053741 / 500000000) ≤ -Real.log (10000 / 11807) ∧
    -Real.log (10000 / 11807) ≤ (166107483 / 1000000000) := by
  have h := checkLog_sound (w := (1807 / 21807)) (n := 12)
    (lo := (83053741 / 500000000)) (hi := (166107483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11807 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11807 / 10000) = 1/(10000 / 11807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4255 : Bounds (83053741 / 500000000) (166107483 / 1000000000) (Real.log (11807 / 10000)) := by
  have h := reflection_log_4255_neg
  have he : Real.log (11807 / 10000) = -Real.log (10000 / 11807) := by
    rw [show ((11807 / 10000) : ℝ) = ((10000 / 11807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4256_neg : (199304961 / 1000000000) ≤ -Real.log (8193 / 10000) ∧
    -Real.log (8193 / 10000) ≤ (99652481 / 500000000) := by
  have h := checkLog_sound (w := (1807 / 18193)) (n := 12)
    (lo := (199304961 / 1000000000)) (hi := (99652481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8193) = 1/(8193 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4256 : Bounds (-99652481 / 500000000) (-199304961 / 1000000000) (Real.log (8193 / 10000)) := by
  have h := reflection_log_4256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4257_neg : (180683 / 1000000000) ≤ -Real.log (10000000 / 10001807) ∧
    -Real.log (10000000 / 10001807) ≤ (45171 / 250000000) := by
  have h := checkLog_sound (w := (1807 / 20001807)) (n := 12)
    (lo := (180683 / 1000000000)) (hi := (45171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001807 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001807 / 10000000) = 1/(10000000 / 10001807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4257 : Bounds (180683 / 1000000000) (45171 / 250000000) (Real.log (10001807 / 10000000)) := by
  have h := reflection_log_4257_neg
  have he : Real.log (10001807 / 10000000) = -Real.log (10000000 / 10001807) := by
    rw [show ((10001807 / 10000000) : ℝ) = ((10000000 / 10001807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4258_neg : (45179 / 250000000) ≤ -Real.log (9998193 / 10000000) ∧
    -Real.log (9998193 / 10000000) ≤ (180717 / 1000000000) := by
  have h := checkLog_sound (w := (1807 / 19998193)) (n := 12)
    (lo := (45179 / 250000000)) (hi := (180717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998193) = 1/(9998193 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4258 : Bounds (-180717 / 1000000000) (-45179 / 250000000) (Real.log (9998193 / 10000000)) := by
  have h := reflection_log_4258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4259_neg : (17372373 / 200000000) ≤ -Real.log (500000 / 545373) ∧
    -Real.log (500000 / 545373) ≤ (43430933 / 500000000) := by
  have h := checkLog_sound (w := (45373 / 1045373)) (n := 12)
    (lo := (17372373 / 200000000)) (hi := (43430933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545373 / 500000) = 1/(500000 / 545373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4259 : Bounds (17372373 / 200000000) (43430933 / 500000000) (Real.log (545373 / 500000)) := by
  have h := reflection_log_4259_neg
  have he : Real.log (545373 / 500000) = -Real.log (500000 / 545373) := by
    rw [show ((545373 / 500000) : ℝ) = ((500000 / 545373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4260_neg : (19026159 / 200000000) ≤ -Real.log (454627 / 500000) ∧
    -Real.log (454627 / 500000) ≤ (23782699 / 250000000) := by
  have h := checkLog_sound (w := (45373 / 954627)) (n := 12)
    (lo := (19026159 / 200000000)) (hi := (23782699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454627) = 1/(454627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4260 : Bounds (-23782699 / 250000000) (-19026159 / 200000000) (Real.log (454627 / 500000)) := by
  have h := reflection_log_4260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4261_neg : (696589 / 8000000) ≤ -Real.log (1000000 / 1090977) ∧
    -Real.log (1000000 / 1090977) ≤ (43536813 / 500000000) := by
  have h := checkLog_sound (w := (90977 / 2090977)) (n := 12)
    (lo := (696589 / 8000000)) (hi := (43536813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090977 / 1000000) = 1/(1000000 / 1090977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4261 : Bounds (696589 / 8000000) (43536813 / 500000000) (Real.log (1090977 / 1000000)) := by
  have h := reflection_log_4261_neg
  have he : Real.log (1090977 / 1000000) = -Real.log (1000000 / 1090977) := by
    rw [show ((1090977 / 1000000) : ℝ) = ((1000000 / 1090977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4262_neg : (47692441 / 500000000) ≤ -Real.log (909023 / 1000000) ∧
    -Real.log (909023 / 1000000) ≤ (95384883 / 1000000000) := by
  have h := checkLog_sound (w := (90977 / 1909023)) (n := 12)
    (lo := (47692441 / 500000000)) (hi := (95384883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909023) = 1/(909023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4262 : Bounds (-95384883 / 1000000000) (-47692441 / 500000000) (Real.log (909023 / 1000000)) := by
  have h := reflection_log_4262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4263_neg : (8311257 / 1000000000) ≤ -Real.log (991723185471 / 1000000000000) ∧
    -Real.log (991723185471 / 1000000000000) ≤ (4155629 / 500000000) := by
  have h := checkLog_sound (w := (8276814529 / 1991723185471)) (n := 12)
    (lo := (8311257 / 1000000000)) (hi := (4155629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991723185471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991723185471) = 1/(991723185471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4263 : Bounds (-4155629 / 500000000) (-8311257 / 1000000000) (Real.log (991723185471 / 1000000000000)) := by
  have h := reflection_log_4263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4264_neg : (826893 / 100000000) ≤ -Real.log (247941290871 / 250000000000) ∧
    -Real.log (247941290871 / 250000000000) ≤ (8268931 / 1000000000) := by
  have h := checkLog_sound (w := (2058709129 / 497941290871)) (n := 12)
    (lo := (826893 / 100000000)) (hi := (8268931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247941290871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247941290871) = 1/(247941290871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4264 : Bounds (-8268931 / 1000000000) (-826893 / 100000000) (Real.log (247941290871 / 250000000000)) := by
  have h := reflection_log_4264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4265_neg : (181992661 / 1000000000) ≤ -Real.log (125000000000 / 149950673849) ∧
    -Real.log (125000000000 / 149950673849) ≤ (90996331 / 500000000) := by
  have h := checkLog_sound (w := (24950673849 / 274950673849)) (n := 12)
    (lo := (181992661 / 1000000000)) (hi := (90996331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149950673849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149950673849 / 125000000000) = 1/(125000000000 / 149950673849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4265 : Bounds (181992661 / 1000000000) (90996331 / 500000000) (Real.log (149950673849 / 125000000000)) := by
  have h := reflection_log_4265_neg
  have he : Real.log (149950673849 / 125000000000) = -Real.log (125000000000 / 149950673849) := by
    rw [show ((149950673849 / 125000000000) : ℝ) = ((125000000000 / 149950673849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4266_neg : (182458507 / 1000000000) ≤ -Real.log (500000000000 / 600082176139) ∧
    -Real.log (500000000000 / 600082176139) ≤ (45614627 / 250000000) := by
  have h := checkLog_sound (w := (100082176139 / 1100082176139)) (n := 12)
    (lo := (182458507 / 1000000000)) (hi := (45614627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600082176139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600082176139 / 500000000000) = 1/(500000000000 / 600082176139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4266 : Bounds (182458507 / 1000000000) (45614627 / 250000000) (Real.log (600082176139 / 500000000000)) := by
  have h := reflection_log_4266_neg
  have he : Real.log (600082176139 / 500000000000) = -Real.log (500000000000 / 600082176139) := by
    rw [show ((600082176139 / 500000000000) : ℝ) = ((500000000000 / 600082176139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4267_neg : (365205697 / 1000000000) ≤ -Real.log (500000000000 / 720405174517) ∧
    -Real.log (500000000000 / 720405174517) ≤ (182602849 / 500000000) := by
  have h := checkLog_sound (w := (220405174517 / 1220405174517)) (n := 12)
    (lo := (365205697 / 1000000000)) (hi := (182602849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720405174517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720405174517 / 500000000000) = 1/(500000000000 / 720405174517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4267 : Bounds (365205697 / 1000000000) (182602849 / 500000000) (Real.log (720405174517 / 500000000000)) := by
  have h := reflection_log_4267_neg
  have he : Real.log (720405174517 / 500000000000) = -Real.log (500000000000 / 720405174517) := by
    rw [show ((720405174517 / 500000000000) : ℝ) = ((500000000000 / 720405174517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4268_neg : (91353111 / 250000000) ≤ -Real.log (62500000000 / 90069266447) ∧
    -Real.log (62500000000 / 90069266447) ≤ (73082489 / 200000000) := by
  have h := checkLog_sound (w := (27569266447 / 152569266447)) (n := 12)
    (lo := (91353111 / 250000000)) (hi := (73082489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90069266447 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90069266447 / 62500000000) = 1/(62500000000 / 90069266447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4268 : Bounds (91353111 / 250000000) (73082489 / 200000000) (Real.log (90069266447 / 62500000000)) := by
  have h := reflection_log_4268_neg
  have he : Real.log (90069266447 / 62500000000) = -Real.log (62500000000 / 90069266447) := by
    rw [show ((90069266447 / 62500000000) : ℝ) = ((62500000000 / 90069266447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4269_neg : (83096087 / 500000000) ≤ -Real.log (625 / 738) ∧
    -Real.log (625 / 738) ≤ (6647687 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1363)) (n := 12)
    (lo := (83096087 / 500000000)) (hi := (6647687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738 / 625) = 1/(625 / 738) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4269 : Bounds (83096087 / 500000000) (6647687 / 40000000) (Real.log (738 / 625)) := by
  have h := reflection_log_4269_neg
  have he : Real.log (738 / 625) = -Real.log (625 / 738) := by
    rw [show ((738 / 625) : ℝ) = ((625 / 738) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4270_neg : (12464189 / 62500000) ≤ -Real.log (512 / 625) ∧
    -Real.log (512 / 625) ≤ (7977081 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 512) = 1/(512 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4270 : Bounds (-7977081 / 40000000) (-12464189 / 62500000) (Real.log (512 / 625)) := by
  have h := reflection_log_4270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4271_neg : (180783 / 1000000000) ≤ -Real.log (625000 / 625113) ∧
    -Real.log (625000 / 625113) ≤ (11299 / 62500000) := by
  have h := checkLog_sound (w := (113 / 1250113)) (n := 12)
    (lo := (180783 / 1000000000)) (hi := (11299 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625113 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625113 / 625000) = 1/(625000 / 625113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4271 : Bounds (180783 / 1000000000) (11299 / 62500000) (Real.log (625113 / 625000)) := by
  have h := reflection_log_4271_neg
  have he : Real.log (625113 / 625000) = -Real.log (625000 / 625113) := by
    rw [show ((625113 / 625000) : ℝ) = ((625000 / 625113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4272_neg : (11301 / 62500000) ≤ -Real.log (624887 / 625000) ∧
    -Real.log (624887 / 625000) ≤ (180817 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 1249887)) (n := 12)
    (lo := (11301 / 62500000)) (hi := (180817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624887) = 1/(624887 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4272 : Bounds (-180817 / 1000000000) (-11301 / 62500000) (Real.log (624887 / 625000)) := by
  have h := reflection_log_4272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4273_neg : (86908621 / 1000000000) ≤ -Real.log (1000000 / 1090797) ∧
    -Real.log (1000000 / 1090797) ≤ (43454311 / 500000000) := by
  have h := checkLog_sound (w := (90797 / 2090797)) (n := 12)
    (lo := (86908621 / 1000000000)) (hi := (43454311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090797 / 1000000) = 1/(1000000 / 1090797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4273 : Bounds (86908621 / 1000000000) (43454311 / 500000000) (Real.log (1090797 / 1000000)) := by
  have h := reflection_log_4273_neg
  have he : Real.log (1090797 / 1000000) = -Real.log (1000000 / 1090797) := by
    rw [show ((1090797 / 1000000) : ℝ) = ((1000000 / 1090797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4274_neg : (95186887 / 1000000000) ≤ -Real.log (909203 / 1000000) ∧
    -Real.log (909203 / 1000000) ≤ (11898361 / 125000000) := by
  have h := checkLog_sound (w := (90797 / 1909203)) (n := 12)
    (lo := (95186887 / 1000000000)) (hi := (11898361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909203) = 1/(909203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4274 : Bounds (-11898361 / 125000000) (-95186887 / 1000000000) (Real.log (909203 / 1000000)) := by
  have h := reflection_log_4274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4275_neg : (87120371 / 1000000000) ≤ -Real.log (250000 / 272757) ∧
    -Real.log (250000 / 272757) ≤ (21780093 / 250000000) := by
  have h := checkLog_sound (w := (22757 / 522757)) (n := 12)
    (lo := (87120371 / 1000000000)) (hi := (21780093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272757 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272757 / 250000) = 1/(250000 / 272757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4275 : Bounds (87120371 / 1000000000) (21780093 / 250000000) (Real.log (272757 / 250000)) := by
  have h := reflection_log_4275_neg
  have he : Real.log (272757 / 250000) = -Real.log (250000 / 272757) := by
    rw [show ((272757 / 250000) : ℝ) = ((250000 / 272757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4276_neg : (23860247 / 250000000) ≤ -Real.log (227243 / 250000) ∧
    -Real.log (227243 / 250000) ≤ (95440989 / 1000000000) := by
  have h := checkLog_sound (w := (22757 / 477243)) (n := 12)
    (lo := (23860247 / 250000000)) (hi := (95440989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227243) = 1/(227243 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4276 : Bounds (-95440989 / 1000000000) (-23860247 / 250000000) (Real.log (227243 / 250000)) := by
  have h := reflection_log_4276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4277_neg : (8320617 / 1000000000) ≤ -Real.log (61982118951 / 62500000000) ∧
    -Real.log (61982118951 / 62500000000) ≤ (4160309 / 500000000) := by
  have h := checkLog_sound (w := (517881049 / 124482118951)) (n := 12)
    (lo := (8320617 / 1000000000)) (hi := (4160309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61982118951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61982118951) = 1/(61982118951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4277 : Bounds (-4160309 / 500000000) (-8320617 / 1000000000) (Real.log (61982118951 / 62500000000)) := by
  have h := reflection_log_4277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4278_neg : (1655653 / 200000000) ≤ -Real.log (991755904791 / 1000000000000) ∧
    -Real.log (991755904791 / 1000000000000) ≤ (4139133 / 500000000) := by
  have h := checkLog_sound (w := (8244095209 / 1991755904791)) (n := 12)
    (lo := (1655653 / 200000000)) (hi := (4139133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991755904791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991755904791) = 1/(991755904791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4278 : Bounds (-4139133 / 500000000) (-1655653 / 200000000) (Real.log (991755904791 / 1000000000000)) := by
  have h := reflection_log_4278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4279_neg : (182095509 / 1000000000) ≤ -Real.log (500000000000 / 599864386721) ∧
    -Real.log (500000000000 / 599864386721) ≤ (18209551 / 100000000) := by
  have h := checkLog_sound (w := (99864386721 / 1099864386721)) (n := 12)
    (lo := (182095509 / 1000000000)) (hi := (18209551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599864386721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599864386721 / 500000000000) = 1/(500000000000 / 599864386721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4279 : Bounds (182095509 / 1000000000) (18209551 / 100000000) (Real.log (599864386721 / 500000000000)) := by
  have h := reflection_log_4279_neg
  have he : Real.log (599864386721 / 500000000000) = -Real.log (500000000000 / 599864386721) := by
    rw [show ((599864386721 / 500000000000) : ℝ) = ((500000000000 / 599864386721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4280_neg : (182561359 / 1000000000) ≤ -Real.log (250000000000 / 300071949411) ∧
    -Real.log (250000000000 / 300071949411) ≤ (2282017 / 12500000) := by
  have h := checkLog_sound (w := (50071949411 / 550071949411)) (n := 12)
    (lo := (182561359 / 1000000000)) (hi := (2282017 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300071949411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300071949411 / 250000000000) = 1/(250000000000 / 300071949411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4280 : Bounds (182561359 / 1000000000) (2282017 / 12500000) (Real.log (300071949411 / 250000000000)) := by
  have h := reflection_log_4280_neg
  have he : Real.log (300071949411 / 250000000000) = -Real.log (250000000000 / 300071949411) := by
    rw [show ((300071949411 / 250000000000) : ℝ) = ((250000000000 / 300071949411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4281_neg : (91353111 / 250000000) ≤ -Real.log (20000000000 / 28822165263) ∧
    -Real.log (20000000000 / 28822165263) ≤ (73082489 / 200000000) := by
  have h := checkLog_sound (w := (8822165263 / 48822165263)) (n := 12)
    (lo := (91353111 / 250000000)) (hi := (73082489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28822165263 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28822165263 / 20000000000) = 1/(20000000000 / 28822165263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4281 : Bounds (91353111 / 250000000) (73082489 / 200000000) (Real.log (28822165263 / 20000000000)) := by
  have h := reflection_log_4281_neg
  have he : Real.log (28822165263 / 20000000000) = -Real.log (20000000000 / 28822165263) := by
    rw [show ((28822165263 / 20000000000) : ℝ) = ((20000000000 / 28822165263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4282_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4282 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_4282_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4283_neg : (166276859 / 1000000000) ≤ -Real.log (10000 / 11809) ∧
    -Real.log (10000 / 11809) ≤ (8313843 / 50000000) := by
  have h := checkLog_sound (w := (1809 / 21809)) (n := 12)
    (lo := (166276859 / 1000000000)) (hi := (8313843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11809 / 10000) = 1/(10000 / 11809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4283 : Bounds (166276859 / 1000000000) (8313843 / 50000000) (Real.log (11809 / 10000)) := by
  have h := reflection_log_4283_neg
  have he : Real.log (11809 / 10000) = -Real.log (10000 / 11809) := by
    rw [show ((11809 / 10000) : ℝ) = ((10000 / 11809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4284_neg : (99774551 / 500000000) ≤ -Real.log (8191 / 10000) ∧
    -Real.log (8191 / 10000) ≤ (199549103 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 18191)) (n := 12)
    (lo := (99774551 / 500000000)) (hi := (199549103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8191) = 1/(8191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4284 : Bounds (-199549103 / 1000000000) (-99774551 / 500000000) (Real.log (8191 / 10000)) := by
  have h := reflection_log_4284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4285_neg : (180883 / 1000000000) ≤ -Real.log (10000000 / 10001809) ∧
    -Real.log (10000000 / 10001809) ≤ (45221 / 250000000) := by
  have h := checkLog_sound (w := (1809 / 20001809)) (n := 12)
    (lo := (180883 / 1000000000)) (hi := (45221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001809 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001809 / 10000000) = 1/(10000000 / 10001809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4285 : Bounds (180883 / 1000000000) (45221 / 250000000) (Real.log (10001809 / 10000000)) := by
  have h := reflection_log_4285_neg
  have he : Real.log (10001809 / 10000000) = -Real.log (10000000 / 10001809) := by
    rw [show ((10001809 / 10000000) : ℝ) = ((10000000 / 10001809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4286_neg : (45229 / 250000000) ≤ -Real.log (9998191 / 10000000) ∧
    -Real.log (9998191 / 10000000) ≤ (180917 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 19998191)) (n := 12)
    (lo := (45229 / 250000000)) (hi := (180917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998191) = 1/(9998191 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4286 : Bounds (-180917 / 1000000000) (-45229 / 250000000) (Real.log (9998191 / 10000000)) := by
  have h := reflection_log_4286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4287_neg : (695643 / 8000000) ≤ -Real.log (31250 / 34089) ∧
    -Real.log (31250 / 34089) ≤ (5434711 / 62500000) := by
  have h := checkLog_sound (w := (2839 / 65339)) (n := 12)
    (lo := (695643 / 8000000)) (hi := (5434711 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34089 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34089 / 31250) = 1/(31250 / 34089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4287 : Bounds (695643 / 8000000) (5434711 / 62500000) (Real.log (34089 / 31250)) := by
  have h := reflection_log_4287_neg
  have he : Real.log (34089 / 31250) = -Real.log (31250 / 34089) := by
    rw [show ((34089 / 31250) : ℝ) = ((31250 / 34089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


