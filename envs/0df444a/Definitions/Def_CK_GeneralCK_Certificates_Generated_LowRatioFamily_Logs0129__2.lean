-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0129__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0129__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:39:23.936018+00:00
-- url     : https://prove2.me/theorems/61a3ec9d-b7d0-404c-9082-b7f2f52de0d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0129 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0130)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0129 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0130)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0129 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0130)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0129 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0130) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0129 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0130).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0129 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8256_neg : (502301331 / 1000000000) ≤ -Real.log (10000000000 / 16525198939) ∧
    -Real.log (10000000000 / 16525198939) ≤ (125575333 / 250000000) := by
  have h := checkLog_sound (w := (6525198939 / 26525198939)) (n := 12)
    (lo := (502301331 / 1000000000)) (hi := (125575333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16525198939 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16525198939 / 10000000000) = 1/(10000000000 / 16525198939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8256 : Bounds (502301331 / 1000000000) (125575333 / 250000000) (Real.log (16525198939 / 10000000000)) := by
  have h := reflection_log_8256_neg
  have he : Real.log (16525198939 / 10000000000) = -Real.log (10000000000 / 16525198939) := by
    rw [show ((16525198939 / 10000000000) : ℝ) = ((10000000000 / 16525198939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8257_neg : (220339623 / 1000000000) ≤ -Real.log (2000 / 2493) ∧
    -Real.log (2000 / 2493) ≤ (27542453 / 125000000) := by
  have h := checkLog_sound (w := (493 / 4493)) (n := 12)
    (lo := (220339623 / 1000000000)) (hi := (27542453 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2000) = 1/(2000 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8257 : Bounds (220339623 / 1000000000) (27542453 / 125000000) (Real.log (2493 / 2000)) := by
  have h := reflection_log_8257_neg
  have he : Real.log (2493 / 2000) = -Real.log (2000 / 2493) := by
    rw [show ((2493 / 2000) : ℝ) = ((2000 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8258_neg : (14151313 / 50000000) ≤ -Real.log (1507 / 2000) ∧
    -Real.log (1507 / 2000) ≤ (283026261 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 3507)) (n := 12)
    (lo := (14151313 / 50000000)) (hi := (283026261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1507) = 1/(1507 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8258 : Bounds (-283026261 / 1000000000) (-14151313 / 50000000) (Real.log (1507 / 2000)) := by
  have h := reflection_log_8258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8259_neg : (246469 / 1000000000) ≤ -Real.log (2000000 / 2000493) ∧
    -Real.log (2000000 / 2000493) ≤ (24647 / 100000000) := by
  have h := checkLog_sound (w := (493 / 4000493)) (n := 12)
    (lo := (246469 / 1000000000)) (hi := (24647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000493 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000493 / 2000000) = 1/(2000000 / 2000493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8259 : Bounds (246469 / 1000000000) (24647 / 100000000) (Real.log (2000493 / 2000000)) := by
  have h := reflection_log_8259_neg
  have he : Real.log (2000493 / 2000000) = -Real.log (2000000 / 2000493) := by
    rw [show ((2000493 / 2000000) : ℝ) = ((2000000 / 2000493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8260_neg : (24653 / 100000000) ≤ -Real.log (1999507 / 2000000) ∧
    -Real.log (1999507 / 2000000) ≤ (246531 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 3999507)) (n := 12)
    (lo := (24653 / 100000000)) (hi := (246531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999507) = 1/(1999507 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8260 : Bounds (-246531 / 1000000000) (-24653 / 100000000) (Real.log (1999507 / 2000000)) := by
  have h := reflection_log_8260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8261_neg : (117111699 / 1000000000) ≤ -Real.log (200000 / 224849) ∧
    -Real.log (200000 / 224849) ≤ (1171117 / 10000000) := by
  have h := checkLog_sound (w := (24849 / 424849)) (n := 12)
    (lo := (117111699 / 1000000000)) (hi := (1171117 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224849 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224849 / 200000) = 1/(200000 / 224849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8261 : Bounds (117111699 / 1000000000) (1171117 / 10000000) (Real.log (224849 / 200000)) := by
  have h := reflection_log_8261_neg
  have he : Real.log (224849 / 200000) = -Real.log (200000 / 224849) := by
    rw [show ((224849 / 200000) : ℝ) = ((200000 / 224849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8262_neg : (132668907 / 1000000000) ≤ -Real.log (175151 / 200000) ∧
    -Real.log (175151 / 200000) ≤ (33167227 / 250000000) := by
  have h := checkLog_sound (w := (24849 / 375151)) (n := 12)
    (lo := (132668907 / 1000000000)) (hi := (33167227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 175151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 175151) = 1/(175151 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8262 : Bounds (-33167227 / 250000000) (-132668907 / 1000000000) (Real.log (175151 / 200000)) := by
  have h := reflection_log_8262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8263_neg : (117558121 / 1000000000) ≤ -Real.log (1000000 / 1124747) ∧
    -Real.log (1000000 / 1124747) ≤ (58779061 / 500000000) := by
  have h := checkLog_sound (w := (124747 / 2124747)) (n := 12)
    (lo := (117558121 / 1000000000)) (hi := (58779061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124747 / 1000000) = 1/(1000000 / 1124747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8263 : Bounds (117558121 / 1000000000) (58779061 / 500000000) (Real.log (1124747 / 1000000)) := by
  have h := reflection_log_8263_neg
  have he : Real.log (1124747 / 1000000) = -Real.log (1000000 / 1124747) := by
    rw [show ((1124747 / 1000000) : ℝ) = ((1000000 / 1124747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8264_neg : (133242291 / 1000000000) ≤ -Real.log (875253 / 1000000) ∧
    -Real.log (875253 / 1000000) ≤ (33310573 / 250000000) := by
  have h := checkLog_sound (w := (124747 / 1875253)) (n := 12)
    (lo := (133242291 / 1000000000)) (hi := (33310573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875253) = 1/(875253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8264 : Bounds (-33310573 / 250000000) (-133242291 / 1000000000) (Real.log (875253 / 1000000)) := by
  have h := reflection_log_8264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8265_neg : (1568417 / 100000000) ≤ -Real.log (984438185991 / 1000000000000) ∧
    -Real.log (984438185991 / 1000000000000) ≤ (15684171 / 1000000000) := by
  have h := checkLog_sound (w := (15561814009 / 1984438185991)) (n := 12)
    (lo := (1568417 / 100000000)) (hi := (15684171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984438185991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984438185991) = 1/(984438185991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8265 : Bounds (-15684171 / 1000000000) (-1568417 / 100000000) (Real.log (984438185991 / 1000000000000)) := by
  have h := reflection_log_8265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8266_neg : (1944651 / 125000000) ≤ -Real.log (39382527199 / 40000000000) ∧
    -Real.log (39382527199 / 40000000000) ≤ (15557209 / 1000000000) := by
  have h := checkLog_sound (w := (617472801 / 79382527199)) (n := 12)
    (lo := (1944651 / 125000000)) (hi := (15557209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39382527199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39382527199) = 1/(39382527199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8266 : Bounds (-15557209 / 1000000000) (-1944651 / 125000000) (Real.log (39382527199 / 40000000000)) := by
  have h := reflection_log_8266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8267_neg : (124890303 / 500000000) ≤ -Real.log (500000000000 / 641871870557) ∧
    -Real.log (500000000000 / 641871870557) ≤ (249780607 / 1000000000) := by
  have h := checkLog_sound (w := (141871870557 / 1141871870557)) (n := 12)
    (lo := (124890303 / 500000000)) (hi := (249780607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641871870557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641871870557 / 500000000000) = 1/(500000000000 / 641871870557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8267 : Bounds (124890303 / 500000000) (249780607 / 1000000000) (Real.log (641871870557 / 500000000000)) := by
  have h := reflection_log_8267_neg
  have he : Real.log (641871870557 / 500000000000) = -Real.log (500000000000 / 641871870557) := by
    rw [show ((641871870557 / 500000000000) : ℝ) = ((500000000000 / 641871870557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8268_neg : (250800413 / 1000000000) ≤ -Real.log (500000000000 / 642526789397) ∧
    -Real.log (500000000000 / 642526789397) ≤ (125400207 / 500000000) := by
  have h := checkLog_sound (w := (142526789397 / 1142526789397)) (n := 12)
    (lo := (250800413 / 1000000000)) (hi := (125400207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642526789397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642526789397 / 500000000000) = 1/(500000000000 / 642526789397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8268 : Bounds (250800413 / 1000000000) (125400207 / 500000000) (Real.log (642526789397 / 500000000000)) := by
  have h := reflection_log_8268_neg
  have he : Real.log (642526789397 / 500000000000) = -Real.log (500000000000 / 642526789397) := by
    rw [show ((642526789397 / 500000000000) : ℝ) = ((500000000000 / 642526789397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8269_neg : (502301331 / 1000000000) ≤ -Real.log (500000000000 / 826259946949) ∧
    -Real.log (500000000000 / 826259946949) ≤ (125575333 / 250000000) := by
  have h := checkLog_sound (w := (326259946949 / 1326259946949)) (n := 12)
    (lo := (502301331 / 1000000000)) (hi := (125575333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826259946949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826259946949 / 500000000000) = 1/(500000000000 / 826259946949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8269 : Bounds (502301331 / 1000000000) (125575333 / 250000000) (Real.log (826259946949 / 500000000000)) := by
  have h := reflection_log_8269_neg
  have he : Real.log (826259946949 / 500000000000) = -Real.log (500000000000 / 826259946949) := by
    rw [show ((826259946949 / 500000000000) : ℝ) = ((500000000000 / 826259946949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8270_neg : (125841471 / 250000000) ≤ -Real.log (62500000000 / 103392501659) ∧
    -Real.log (62500000000 / 103392501659) ≤ (100673177 / 200000000) := by
  have h := checkLog_sound (w := (40892501659 / 165892501659)) (n := 12)
    (lo := (125841471 / 250000000)) (hi := (100673177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103392501659 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103392501659 / 62500000000) = 1/(62500000000 / 103392501659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8270 : Bounds (125841471 / 250000000) (100673177 / 200000000) (Real.log (103392501659 / 62500000000)) := by
  have h := reflection_log_8270_neg
  have he : Real.log (103392501659 / 62500000000) = -Real.log (62500000000 / 103392501659) := by
    rw [show ((103392501659 / 62500000000) : ℝ) = ((62500000000 / 103392501659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8271_neg : (110370333 / 500000000) ≤ -Real.log (1000 / 1247) ∧
    -Real.log (1000 / 1247) ≤ (220740667 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 2247)) (n := 12)
    (lo := (110370333 / 500000000)) (hi := (220740667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 1000) = 1/(1000 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8271 : Bounds (110370333 / 500000000) (220740667 / 1000000000) (Real.log (1247 / 1000)) := by
  have h := reflection_log_8271_neg
  have he : Real.log (1247 / 1000) = -Real.log (1000 / 1247) := by
    rw [show ((1247 / 1000) : ℝ) = ((1000 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8272_neg : (283690051 / 1000000000) ≤ -Real.log (753 / 1000) ∧
    -Real.log (753 / 1000) ≤ (70922513 / 250000000) := by
  have h := checkLog_sound (w := (247 / 1753)) (n := 12)
    (lo := (283690051 / 1000000000)) (hi := (70922513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 753) = 1/(753 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8272 : Bounds (-70922513 / 250000000) (-283690051 / 1000000000) (Real.log (753 / 1000)) := by
  have h := reflection_log_8272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8273_neg : (246969 / 1000000000) ≤ -Real.log (1000000 / 1000247) ∧
    -Real.log (1000000 / 1000247) ≤ (24697 / 100000000) := by
  have h := checkLog_sound (w := (247 / 2000247)) (n := 12)
    (lo := (246969 / 1000000000)) (hi := (24697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000247 / 1000000) = 1/(1000000 / 1000247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8273 : Bounds (246969 / 1000000000) (24697 / 100000000) (Real.log (1000247 / 1000000)) := by
  have h := reflection_log_8273_neg
  have he : Real.log (1000247 / 1000000) = -Real.log (1000000 / 1000247) := by
    rw [show ((1000247 / 1000000) : ℝ) = ((1000000 / 1000247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8274_neg : (24703 / 100000000) ≤ -Real.log (999753 / 1000000) ∧
    -Real.log (999753 / 1000000) ≤ (247031 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1999753)) (n := 12)
    (lo := (24703 / 100000000)) (hi := (247031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999753) = 1/(999753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8274 : Bounds (-247031 / 1000000000) (-24703 / 100000000) (Real.log (999753 / 1000000)) := by
  have h := reflection_log_8274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8275_neg : (2933529 / 25000000) ≤ -Real.log (1000000 / 1124503) ∧
    -Real.log (1000000 / 1124503) ≤ (117341161 / 1000000000) := by
  have h := checkLog_sound (w := (124503 / 2124503)) (n := 12)
    (lo := (2933529 / 25000000)) (hi := (117341161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124503 / 1000000) = 1/(1000000 / 1124503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8275 : Bounds (2933529 / 25000000) (117341161 / 1000000000) (Real.log (1124503 / 1000000)) := by
  have h := reflection_log_8275_neg
  have he : Real.log (1124503 / 1000000) = -Real.log (1000000 / 1124503) := by
    rw [show ((1124503 / 1000000) : ℝ) = ((1000000 / 1124503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8276_neg : (132963553 / 1000000000) ≤ -Real.log (875497 / 1000000) ∧
    -Real.log (875497 / 1000000) ≤ (66481777 / 500000000) := by
  have h := checkLog_sound (w := (124503 / 1875497)) (n := 12)
    (lo := (132963553 / 1000000000)) (hi := (66481777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875497) = 1/(875497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8276 : Bounds (-66481777 / 500000000) (-132963553 / 1000000000) (Real.log (875497 / 1000000)) := by
  have h := reflection_log_8276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8277_neg : (7361773 / 62500000) ≤ -Real.log (500000 / 562503) ∧
    -Real.log (500000 / 562503) ≤ (117788369 / 1000000000) := by
  have h := checkLog_sound (w := (62503 / 1062503)) (n := 12)
    (lo := (7361773 / 62500000)) (hi := (117788369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562503 / 500000) = 1/(500000 / 562503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8277 : Bounds (7361773 / 62500000) (117788369 / 1000000000) (Real.log (562503 / 500000)) := by
  have h := reflection_log_8277_neg
  have he : Real.log (562503 / 500000) = -Real.log (500000 / 562503) := by
    rw [show ((562503 / 500000) : ℝ) = ((500000 / 562503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8278_neg : (133538249 / 1000000000) ≤ -Real.log (437497 / 500000) ∧
    -Real.log (437497 / 500000) ≤ (534153 / 4000000) := by
  have h := checkLog_sound (w := (62503 / 937497)) (n := 12)
    (lo := (133538249 / 1000000000)) (hi := (534153 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437497) = 1/(437497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8278 : Bounds (-534153 / 4000000) (-133538249 / 1000000000) (Real.log (437497 / 500000)) := by
  have h := reflection_log_8278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8279_neg : (393747 / 25000000) ≤ -Real.log (246093374991 / 250000000000) ∧
    -Real.log (246093374991 / 250000000000) ≤ (15749881 / 1000000000) := by
  have h := checkLog_sound (w := (3906625009 / 496093374991)) (n := 12)
    (lo := (393747 / 25000000)) (hi := (15749881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246093374991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246093374991) = 1/(246093374991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8279 : Bounds (-15749881 / 1000000000) (-393747 / 25000000) (Real.log (246093374991 / 250000000000)) := by
  have h := reflection_log_8279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8280_neg : (15622393 / 1000000000) ≤ -Real.log (984499002991 / 1000000000000) ∧
    -Real.log (984499002991 / 1000000000000) ≤ (7811197 / 500000000) := by
  have h := checkLog_sound (w := (15500997009 / 1984499002991)) (n := 12)
    (lo := (15622393 / 1000000000)) (hi := (7811197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984499002991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984499002991) = 1/(984499002991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8280 : Bounds (-7811197 / 500000000) (-15622393 / 1000000000) (Real.log (984499002991 / 1000000000000)) := by
  have h := reflection_log_8280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8281_neg : (125152357 / 500000000) ≤ -Real.log (500000000000 / 642208368503) ∧
    -Real.log (500000000000 / 642208368503) ≤ (50060943 / 200000000) := by
  have h := checkLog_sound (w := (142208368503 / 1142208368503)) (n := 12)
    (lo := (125152357 / 500000000)) (hi := (50060943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642208368503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642208368503 / 500000000000) = 1/(500000000000 / 642208368503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8281 : Bounds (125152357 / 500000000) (50060943 / 200000000) (Real.log (642208368503 / 500000000000)) := by
  have h := reflection_log_8281_neg
  have he : Real.log (642208368503 / 500000000000) = -Real.log (500000000000 / 642208368503) := by
    rw [show ((642208368503 / 500000000000) : ℝ) = ((500000000000 / 642208368503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8282_neg : (125663309 / 500000000) ≤ -Real.log (250000000000 / 321432489823) ∧
    -Real.log (250000000000 / 321432489823) ≤ (251326619 / 1000000000) := by
  have h := checkLog_sound (w := (71432489823 / 571432489823)) (n := 12)
    (lo := (125663309 / 500000000)) (hi := (251326619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321432489823 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321432489823 / 250000000000) = 1/(250000000000 / 321432489823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8282 : Bounds (125663309 / 500000000) (251326619 / 1000000000) (Real.log (321432489823 / 250000000000)) := by
  have h := reflection_log_8282_neg
  have he : Real.log (321432489823 / 250000000000) = -Real.log (250000000000 / 321432489823) := by
    rw [show ((321432489823 / 250000000000) : ℝ) = ((250000000000 / 321432489823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8283_neg : (125841471 / 250000000) ≤ -Real.log (500000000000 / 827140013271) ∧
    -Real.log (500000000000 / 827140013271) ≤ (100673177 / 200000000) := by
  have h := checkLog_sound (w := (327140013271 / 1327140013271)) (n := 12)
    (lo := (125841471 / 250000000)) (hi := (100673177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827140013271 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827140013271 / 500000000000) = 1/(500000000000 / 827140013271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8283 : Bounds (125841471 / 250000000) (100673177 / 200000000) (Real.log (827140013271 / 500000000000)) := by
  have h := reflection_log_8283_neg
  have he : Real.log (827140013271 / 500000000000) = -Real.log (500000000000 / 827140013271) := by
    rw [show ((827140013271 / 500000000000) : ℝ) = ((500000000000 / 827140013271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8284_neg : (504430717 / 1000000000) ≤ -Real.log (25000000000 / 41401062417) ∧
    -Real.log (25000000000 / 41401062417) ≤ (252215359 / 500000000) := by
  have h := checkLog_sound (w := (16401062417 / 66401062417)) (n := 12)
    (lo := (504430717 / 1000000000)) (hi := (252215359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41401062417 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41401062417 / 25000000000) = 1/(25000000000 / 41401062417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8284 : Bounds (504430717 / 1000000000) (252215359 / 500000000) (Real.log (41401062417 / 25000000000)) := by
  have h := reflection_log_8284_neg
  have he : Real.log (41401062417 / 25000000000) = -Real.log (25000000000 / 41401062417) := by
    rw [show ((41401062417 / 25000000000) : ℝ) = ((25000000000 / 41401062417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8285_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8285 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_8285_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8286_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8286 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_8286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8287_neg : (247469 / 1000000000) ≤ -Real.log (400000 / 400099) ∧
    -Real.log (400000 / 400099) ≤ (24747 / 100000000) := by
  have h := checkLog_sound (w := (99 / 800099)) (n := 12)
    (lo := (247469 / 1000000000)) (hi := (24747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400099 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400099 / 400000) = 1/(400000 / 400099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8287 : Bounds (247469 / 1000000000) (24747 / 100000000) (Real.log (400099 / 400000)) := by
  have h := reflection_log_8287_neg
  have he : Real.log (400099 / 400000) = -Real.log (400000 / 400099) := by
    rw [show ((400099 / 400000) : ℝ) = ((400000 / 400099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8288_neg : (24753 / 100000000) ≤ -Real.log (399901 / 400000) ∧
    -Real.log (399901 / 400000) ≤ (247531 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 799901)) (n := 12)
    (lo := (24753 / 100000000)) (hi := (247531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399901) = 1/(399901 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8288 : Bounds (-247531 / 1000000000) (-24753 / 100000000) (Real.log (399901 / 400000)) := by
  have h := reflection_log_8288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8289_neg : (14696321 / 125000000) ≤ -Real.log (1000000 / 1124761) ∧
    -Real.log (1000000 / 1124761) ≤ (117570569 / 1000000000) := by
  have h := checkLog_sound (w := (124761 / 2124761)) (n := 12)
    (lo := (14696321 / 125000000)) (hi := (117570569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124761 / 1000000) = 1/(1000000 / 1124761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8289 : Bounds (14696321 / 125000000) (117570569 / 1000000000) (Real.log (1124761 / 1000000)) := by
  have h := reflection_log_8289_neg
  have he : Real.log (1124761 / 1000000) = -Real.log (1000000 / 1124761) := by
    rw [show ((1124761 / 1000000) : ℝ) = ((1000000 / 1124761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8290_neg : (133258287 / 1000000000) ≤ -Real.log (875239 / 1000000) ∧
    -Real.log (875239 / 1000000) ≤ (8328643 / 62500000) := by
  have h := checkLog_sound (w := (124761 / 1875239)) (n := 12)
    (lo := (133258287 / 1000000000)) (hi := (8328643 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875239) = 1/(875239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8290 : Bounds (-8328643 / 62500000) (-133258287 / 1000000000) (Real.log (875239 / 1000000)) := by
  have h := reflection_log_8290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8291_neg : (118018563 / 1000000000) ≤ -Real.log (200000 / 225053) ∧
    -Real.log (200000 / 225053) ≤ (29504641 / 250000000) := by
  have h := checkLog_sound (w := (25053 / 425053)) (n := 12)
    (lo := (118018563 / 1000000000)) (hi := (29504641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225053 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225053 / 200000) = 1/(200000 / 225053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8291 : Bounds (118018563 / 1000000000) (29504641 / 250000000) (Real.log (225053 / 200000)) := by
  have h := reflection_log_8291_neg
  have he : Real.log (225053 / 200000) = -Real.log (200000 / 225053) := by
    rw [show ((225053 / 200000) : ℝ) = ((200000 / 225053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8292_neg : (26766859 / 200000000) ≤ -Real.log (174947 / 200000) ∧
    -Real.log (174947 / 200000) ≤ (16729287 / 125000000) := by
  have h := checkLog_sound (w := (25053 / 374947)) (n := 12)
    (lo := (26766859 / 200000000)) (hi := (16729287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174947) = 1/(174947 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8292 : Bounds (-16729287 / 125000000) (-26766859 / 200000000) (Real.log (174947 / 200000)) := by
  have h := reflection_log_8292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8293_neg : (3953933 / 250000000) ≤ -Real.log (39372347191 / 40000000000) ∧
    -Real.log (39372347191 / 40000000000) ≤ (15815733 / 1000000000) := by
  have h := checkLog_sound (w := (627652809 / 79372347191)) (n := 12)
    (lo := (3953933 / 250000000)) (hi := (15815733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39372347191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39372347191) = 1/(39372347191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8293 : Bounds (-15815733 / 1000000000) (-3953933 / 250000000) (Real.log (39372347191 / 40000000000)) := by
  have h := reflection_log_8293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8294_neg : (7843859 / 500000000) ≤ -Real.log (984434692879 / 1000000000000) ∧
    -Real.log (984434692879 / 1000000000000) ≤ (15687719 / 1000000000) := by
  have h := checkLog_sound (w := (15565307121 / 1984434692879)) (n := 12)
    (lo := (7843859 / 500000000)) (hi := (15687719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984434692879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984434692879) = 1/(984434692879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8294 : Bounds (-15687719 / 1000000000) (-7843859 / 500000000) (Real.log (984434692879 / 1000000000000)) := by
  have h := reflection_log_8294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8295_neg : (50165771 / 200000000) ≤ -Real.log (500000000000 / 642545064833) ∧
    -Real.log (500000000000 / 642545064833) ≤ (31353607 / 125000000) := by
  have h := checkLog_sound (w := (142545064833 / 1142545064833)) (n := 12)
    (lo := (50165771 / 200000000)) (hi := (31353607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642545064833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642545064833 / 500000000000) = 1/(500000000000 / 642545064833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8295 : Bounds (50165771 / 200000000) (31353607 / 125000000) (Real.log (642545064833 / 500000000000)) := by
  have h := reflection_log_8295_neg
  have he : Real.log (642545064833 / 500000000000) = -Real.log (500000000000 / 642545064833) := by
    rw [show ((642545064833 / 500000000000) : ℝ) = ((500000000000 / 642545064833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8296_neg : (251852859 / 1000000000) ≤ -Real.log (125000000000 / 160800842541) ∧
    -Real.log (125000000000 / 160800842541) ≤ (12592643 / 50000000) := by
  have h := checkLog_sound (w := (35800842541 / 285800842541)) (n := 12)
    (lo := (251852859 / 1000000000)) (hi := (12592643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160800842541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160800842541 / 125000000000) = 1/(125000000000 / 160800842541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8296 : Bounds (251852859 / 1000000000) (12592643 / 50000000) (Real.log (160800842541 / 125000000000)) := by
  have h := reflection_log_8296_neg
  have he : Real.log (160800842541 / 125000000000) = -Real.log (125000000000 / 160800842541) := by
    rw [show ((160800842541 / 125000000000) : ℝ) = ((125000000000 / 160800842541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8297_neg : (504430717 / 1000000000) ≤ -Real.log (500000000000 / 828021248339) ∧
    -Real.log (500000000000 / 828021248339) ≤ (252215359 / 500000000) := by
  have h := checkLog_sound (w := (328021248339 / 1328021248339)) (n := 12)
    (lo := (504430717 / 1000000000)) (hi := (252215359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828021248339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828021248339 / 500000000000) = 1/(500000000000 / 828021248339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8297 : Bounds (504430717 / 1000000000) (252215359 / 500000000) (Real.log (828021248339 / 500000000000)) := by
  have h := reflection_log_8297_neg
  have he : Real.log (828021248339 / 500000000000) = -Real.log (500000000000 / 828021248339) := by
    rw [show ((828021248339 / 500000000000) : ℝ) = ((500000000000 / 828021248339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8298_neg : (505495831 / 1000000000) ≤ -Real.log (250000000000 / 414451827243) ∧
    -Real.log (250000000000 / 414451827243) ≤ (63186979 / 125000000) := by
  have h := checkLog_sound (w := (164451827243 / 664451827243)) (n := 12)
    (lo := (505495831 / 1000000000)) (hi := (63186979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414451827243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414451827243 / 250000000000) = 1/(250000000000 / 414451827243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8298 : Bounds (505495831 / 1000000000) (63186979 / 125000000) (Real.log (414451827243 / 250000000000)) := by
  have h := reflection_log_8298_neg
  have he : Real.log (414451827243 / 250000000000) = -Real.log (250000000000 / 414451827243) := by
    rw [show ((414451827243 / 250000000000) : ℝ) = ((250000000000 / 414451827243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8299_neg : (221542269 / 1000000000) ≤ -Real.log (125 / 156) ∧
    -Real.log (125 / 156) ≤ (22154227 / 100000000) := by
  have h := checkLog_sound (w := (31 / 281)) (n := 12)
    (lo := (221542269 / 1000000000)) (hi := (22154227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156 / 125) = 1/(125 / 156) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8299 : Bounds (221542269 / 1000000000) (22154227 / 100000000) (Real.log (156 / 125)) := by
  have h := reflection_log_8299_neg
  have he : Real.log (156 / 125) = -Real.log (125 / 156) := by
    rw [show ((156 / 125) : ℝ) = ((125 / 156) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8300_neg : (57003791 / 200000000) ≤ -Real.log (94 / 125) ∧
    -Real.log (94 / 125) ≤ (71254739 / 250000000) := by
  have h := checkLog_sound (w := (31 / 219)) (n := 12)
    (lo := (57003791 / 200000000)) (hi := (71254739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 94) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 94) = 1/(94 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8300 : Bounds (-71254739 / 250000000) (-57003791 / 200000000) (Real.log (94 / 125)) := by
  have h := reflection_log_8300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8301_neg : (247969 / 1000000000) ≤ -Real.log (125000 / 125031) ∧
    -Real.log (125000 / 125031) ≤ (24797 / 100000000) := by
  have h := checkLog_sound (w := (31 / 250031)) (n := 12)
    (lo := (247969 / 1000000000)) (hi := (24797 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125031 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125031 / 125000) = 1/(125000 / 125031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8301 : Bounds (247969 / 1000000000) (24797 / 100000000) (Real.log (125031 / 125000)) := by
  have h := reflection_log_8301_neg
  have he : Real.log (125031 / 125000) = -Real.log (125000 / 125031) := by
    rw [show ((125031 / 125000) : ℝ) = ((125000 / 125031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8302_neg : (24803 / 100000000) ≤ -Real.log (124969 / 125000) ∧
    -Real.log (124969 / 125000) ≤ (248031 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 249969)) (n := 12)
    (lo := (24803 / 100000000)) (hi := (248031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124969) = 1/(124969 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8302 : Bounds (-248031 / 1000000000) (-24803 / 100000000) (Real.log (124969 / 125000)) := by
  have h := reflection_log_8302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8303_neg : (29449981 / 250000000) ≤ -Real.log (1000000 / 1125019) ∧
    -Real.log (1000000 / 1125019) ≤ (4711997 / 40000000) := by
  have h := checkLog_sound (w := (125019 / 2125019)) (n := 12)
    (lo := (29449981 / 250000000)) (hi := (4711997 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1125019 / 1000000) = 1/(1000000 / 1125019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8303 : Bounds (29449981 / 250000000) (4711997 / 40000000) (Real.log (1125019 / 1000000)) := by
  have h := reflection_log_8303_neg
  have he : Real.log (1125019 / 1000000) = -Real.log (1000000 / 1125019) := by
    rw [show ((1125019 / 1000000) : ℝ) = ((1000000 / 1125019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8304_neg : (133553107 / 1000000000) ≤ -Real.log (874981 / 1000000) ∧
    -Real.log (874981 / 1000000) ≤ (33388277 / 250000000) := by
  have h := checkLog_sound (w := (125019 / 1874981)) (n := 12)
    (lo := (133553107 / 1000000000)) (hi := (33388277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 874981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 874981) = 1/(874981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8304 : Bounds (-33388277 / 250000000) (-133553107 / 1000000000) (Real.log (874981 / 1000000)) := by
  have h := reflection_log_8304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8305_neg : (461909 / 3906250) ≤ -Real.log (250000 / 281381) ∧
    -Real.log (250000 / 281381) ≤ (23649741 / 200000000) := by
  have h := checkLog_sound (w := (31381 / 531381)) (n := 12)
    (lo := (461909 / 3906250)) (hi := (23649741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281381 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281381 / 250000) = 1/(250000 / 281381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8305 : Bounds (461909 / 3906250) (23649741 / 200000000) (Real.log (281381 / 250000)) := by
  have h := reflection_log_8305_neg
  have he : Real.log (281381 / 250000) = -Real.log (250000 / 281381) := by
    rw [show ((281381 / 250000) : ℝ) = ((250000 / 281381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8306_neg : (134130429 / 1000000000) ≤ -Real.log (218619 / 250000) ∧
    -Real.log (218619 / 250000) ≤ (13413043 / 100000000) := by
  have h := checkLog_sound (w := (31381 / 468619)) (n := 12)
    (lo := (134130429 / 1000000000)) (hi := (13413043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 218619) = 1/(218619 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8306 : Bounds (-13413043 / 100000000) (-134130429 / 1000000000) (Real.log (218619 / 250000)) := by
  have h := reflection_log_8306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8307_neg : (3970431 / 250000000) ≤ -Real.log (61515232839 / 62500000000) ∧
    -Real.log (61515232839 / 62500000000) ≤ (635269 / 40000000) := by
  have h := checkLog_sound (w := (984767161 / 124015232839)) (n := 12)
    (lo := (3970431 / 250000000)) (hi := (635269 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61515232839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61515232839) = 1/(61515232839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8307 : Bounds (-635269 / 40000000) (-3970431 / 250000000) (Real.log (61515232839 / 62500000000)) := by
  have h := reflection_log_8307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8308_neg : (7876591 / 500000000) ≤ -Real.log (984370249639 / 1000000000000) ∧
    -Real.log (984370249639 / 1000000000000) ≤ (15753183 / 1000000000) := by
  have h := checkLog_sound (w := (15629750361 / 1984370249639)) (n := 12)
    (lo := (7876591 / 500000000)) (hi := (15753183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984370249639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984370249639) = 1/(984370249639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8308 : Bounds (-15753183 / 1000000000) (-7876591 / 500000000) (Real.log (984370249639 / 1000000000000)) := by
  have h := reflection_log_8308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8309_neg : (251353031 / 1000000000) ≤ -Real.log (250000000000 / 321440979861) ∧
    -Real.log (250000000000 / 321440979861) ≤ (31419129 / 125000000) := by
  have h := checkLog_sound (w := (71440979861 / 571440979861)) (n := 12)
    (lo := (251353031 / 1000000000)) (hi := (31419129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321440979861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321440979861 / 250000000000) = 1/(250000000000 / 321440979861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8309 : Bounds (251353031 / 1000000000) (31419129 / 125000000) (Real.log (321440979861 / 250000000000)) := by
  have h := reflection_log_8309_neg
  have he : Real.log (321440979861 / 250000000000) = -Real.log (250000000000 / 321440979861) := by
    rw [show ((321440979861 / 250000000000) : ℝ) = ((250000000000 / 321440979861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8310_neg : (126189567 / 500000000) ≤ -Real.log (500000000000 / 643541961129) ∧
    -Real.log (500000000000 / 643541961129) ≤ (50475827 / 200000000) := by
  have h := checkLog_sound (w := (143541961129 / 1143541961129)) (n := 12)
    (lo := (126189567 / 500000000)) (hi := (50475827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643541961129 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643541961129 / 500000000000) = 1/(500000000000 / 643541961129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8310 : Bounds (126189567 / 500000000) (50475827 / 200000000) (Real.log (643541961129 / 500000000000)) := by
  have h := reflection_log_8310_neg
  have he : Real.log (643541961129 / 500000000000) = -Real.log (500000000000 / 643541961129) := by
    rw [show ((643541961129 / 500000000000) : ℝ) = ((500000000000 / 643541961129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8311_neg : (505495831 / 1000000000) ≤ -Real.log (100000000000 / 165780730897) ∧
    -Real.log (100000000000 / 165780730897) ≤ (63186979 / 125000000) := by
  have h := checkLog_sound (w := (65780730897 / 265780730897)) (n := 12)
    (lo := (505495831 / 1000000000)) (hi := (63186979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165780730897 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165780730897 / 100000000000) = 1/(100000000000 / 165780730897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8311 : Bounds (505495831 / 1000000000) (63186979 / 125000000) (Real.log (165780730897 / 100000000000)) := by
  have h := reflection_log_8311_neg
  have he : Real.log (165780730897 / 100000000000) = -Real.log (100000000000 / 165780730897) := by
    rw [show ((165780730897 / 100000000000) : ℝ) = ((100000000000 / 165780730897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8312_neg : (63320153 / 125000000) ≤ -Real.log (500000000000 / 829787234043) ∧
    -Real.log (500000000000 / 829787234043) ≤ (20262449 / 40000000) := by
  have h := checkLog_sound (w := (329787234043 / 1329787234043)) (n := 12)
    (lo := (63320153 / 125000000)) (hi := (20262449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829787234043 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829787234043 / 500000000000) = 1/(500000000000 / 829787234043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8312 : Bounds (63320153 / 125000000) (20262449 / 40000000) (Real.log (829787234043 / 500000000000)) := by
  have h := reflection_log_8312_neg
  have he : Real.log (829787234043 / 500000000000) = -Real.log (500000000000 / 829787234043) := by
    rw [show ((829787234043 / 500000000000) : ℝ) = ((500000000000 / 829787234043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8313_neg : (22194283 / 100000000) ≤ -Real.log (2000 / 2497) ∧
    -Real.log (2000 / 2497) ≤ (221942831 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 4497)) (n := 12)
    (lo := (22194283 / 100000000)) (hi := (221942831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 2000) = 1/(2000 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8313 : Bounds (22194283 / 100000000) (221942831 / 1000000000) (Real.log (2497 / 2000)) := by
  have h := reflection_log_8313_neg
  have he : Real.log (2497 / 2000) = -Real.log (2000 / 2497) := by
    rw [show ((2497 / 2000) : ℝ) = ((2000 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8314_neg : (285684069 / 1000000000) ≤ -Real.log (1503 / 2000) ∧
    -Real.log (1503 / 2000) ≤ (28568407 / 100000000) := by
  have h := checkLog_sound (w := (497 / 3503)) (n := 12)
    (lo := (285684069 / 1000000000)) (hi := (28568407 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1503) = 1/(1503 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8314 : Bounds (-28568407 / 100000000) (-285684069 / 1000000000) (Real.log (1503 / 2000)) := by
  have h := reflection_log_8314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8315_neg : (248469 / 1000000000) ≤ -Real.log (2000000 / 2000497) ∧
    -Real.log (2000000 / 2000497) ≤ (24847 / 100000000) := by
  have h := checkLog_sound (w := (497 / 4000497)) (n := 12)
    (lo := (248469 / 1000000000)) (hi := (24847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000497 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000497 / 2000000) = 1/(2000000 / 2000497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8315 : Bounds (248469 / 1000000000) (24847 / 100000000) (Real.log (2000497 / 2000000)) := by
  have h := reflection_log_8315_neg
  have he : Real.log (2000497 / 2000000) = -Real.log (2000000 / 2000497) := by
    rw [show ((2000497 / 2000000) : ℝ) = ((2000000 / 2000497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8316_neg : (24853 / 100000000) ≤ -Real.log (1999503 / 2000000) ∧
    -Real.log (1999503 / 2000000) ≤ (248531 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 3999503)) (n := 12)
    (lo := (24853 / 100000000)) (hi := (248531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999503) = 1/(1999503 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8316 : Bounds (-248531 / 1000000000) (-24853 / 100000000) (Real.log (1999503 / 2000000)) := by
  have h := reflection_log_8316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8317_neg : (29507529 / 250000000) ≤ -Real.log (500000 / 562639) ∧
    -Real.log (500000 / 562639) ≤ (118030117 / 1000000000) := by
  have h := checkLog_sound (w := (62639 / 1062639)) (n := 12)
    (lo := (29507529 / 250000000)) (hi := (118030117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562639 / 500000) = 1/(500000 / 562639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8317 : Bounds (29507529 / 250000000) (118030117 / 1000000000) (Real.log (562639 / 500000)) := by
  have h := reflection_log_8317_neg
  have he : Real.log (562639 / 500000) = -Real.log (500000 / 562639) := by
    rw [show ((562639 / 500000) : ℝ) = ((500000 / 562639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8318_neg : (133849157 / 1000000000) ≤ -Real.log (437361 / 500000) ∧
    -Real.log (437361 / 500000) ≤ (66924579 / 500000000) := by
  have h := checkLog_sound (w := (62639 / 937361)) (n := 12)
    (lo := (133849157 / 1000000000)) (hi := (66924579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437361) = 1/(437361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8318 : Bounds (-66924579 / 500000000) (-133849157 / 1000000000) (Real.log (437361 / 500000)) := by
  have h := reflection_log_8318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8319_neg : (118478793 / 1000000000) ≤ -Real.log (1000000 / 1125783) ∧
    -Real.log (1000000 / 1125783) ≤ (59239397 / 500000000) := by
  have h := checkLog_sound (w := (125783 / 2125783)) (n := 12)
    (lo := (118478793 / 1000000000)) (hi := (59239397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1125783 / 1000000) = 1/(1000000 / 1125783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8319 : Bounds (118478793 / 1000000000) (59239397 / 500000000) (Real.log (1125783 / 1000000)) := by
  have h := reflection_log_8319_neg
  have he : Real.log (1125783 / 1000000) = -Real.log (1000000 / 1125783) := by
    rw [show ((1125783 / 1000000) : ℝ) = ((1000000 / 1125783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0130 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8320_neg : (2688533 / 20000000) ≤ -Real.log (874217 / 1000000) ∧
    -Real.log (874217 / 1000000) ≤ (134426651 / 1000000000) := by
  have h := checkLog_sound (w := (125783 / 1874217)) (n := 12)
    (lo := (2688533 / 20000000)) (hi := (134426651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 874217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 874217) = 1/(874217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8320 : Bounds (-134426651 / 1000000000) (-2688533 / 20000000) (Real.log (874217 / 1000000)) := by
  have h := reflection_log_8320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8321_neg : (996741 / 62500000) ≤ -Real.log (984178636911 / 1000000000000) ∧
    -Real.log (984178636911 / 1000000000000) ≤ (15947857 / 1000000000) := by
  have h := checkLog_sound (w := (15821363089 / 1984178636911)) (n := 12)
    (lo := (996741 / 62500000)) (hi := (15947857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984178636911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984178636911) = 1/(984178636911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8321 : Bounds (-15947857 / 1000000000) (-996741 / 62500000) (Real.log (984178636911 / 1000000000000)) := by
  have h := reflection_log_8321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8322_neg : (15819041 / 1000000000) ≤ -Real.log (246076355679 / 250000000000) ∧
    -Real.log (246076355679 / 250000000000) ≤ (7909521 / 500000000) := by
  have h := checkLog_sound (w := (3923644321 / 496076355679)) (n := 12)
    (lo := (15819041 / 1000000000)) (hi := (7909521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246076355679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246076355679) = 1/(246076355679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8322 : Bounds (-7909521 / 500000000) (-15819041 / 1000000000) (Real.log (246076355679 / 250000000000)) := by
  have h := reflection_log_8322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8323_neg : (251879273 / 1000000000) ≤ -Real.log (500000000000 / 643220360297) ∧
    -Real.log (500000000000 / 643220360297) ≤ (125939637 / 500000000) := by
  have h := checkLog_sound (w := (143220360297 / 1143220360297)) (n := 12)
    (lo := (251879273 / 1000000000)) (hi := (125939637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643220360297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643220360297 / 500000000000) = 1/(500000000000 / 643220360297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8323 : Bounds (251879273 / 1000000000) (125939637 / 500000000) (Real.log (643220360297 / 500000000000)) := by
  have h := reflection_log_8323_neg
  have he : Real.log (643220360297 / 500000000000) = -Real.log (500000000000 / 643220360297) := by
    rw [show ((643220360297 / 500000000000) : ℝ) = ((500000000000 / 643220360297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8324_neg : (252905443 / 1000000000) ≤ -Real.log (6250000000 / 8048509409) ∧
    -Real.log (6250000000 / 8048509409) ≤ (63226361 / 250000000) := by
  have h := checkLog_sound (w := (1798509409 / 14298509409)) (n := 12)
    (lo := (252905443 / 1000000000)) (hi := (63226361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8048509409 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8048509409 / 6250000000) = 1/(6250000000 / 8048509409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8324 : Bounds (252905443 / 1000000000) (63226361 / 250000000) (Real.log (8048509409 / 6250000000)) := by
  have h := reflection_log_8324_neg
  have he : Real.log (8048509409 / 6250000000) = -Real.log (6250000000 / 8048509409) := by
    rw [show ((8048509409 / 6250000000) : ℝ) = ((6250000000 / 8048509409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8325_neg : (63320153 / 125000000) ≤ -Real.log (250000000000 / 414893617021) ∧
    -Real.log (250000000000 / 414893617021) ≤ (20262449 / 40000000) := by
  have h := checkLog_sound (w := (164893617021 / 664893617021)) (n := 12)
    (lo := (63320153 / 125000000)) (hi := (20262449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414893617021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414893617021 / 250000000000) = 1/(250000000000 / 414893617021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8325 : Bounds (63320153 / 125000000) (20262449 / 40000000) (Real.log (414893617021 / 250000000000)) := by
  have h := reflection_log_8325_neg
  have he : Real.log (414893617021 / 250000000000) = -Real.log (250000000000 / 414893617021) := by
    rw [show ((414893617021 / 250000000000) : ℝ) = ((250000000000 / 414893617021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8326_neg : (5076269 / 10000000) ≤ -Real.log (100000000000 / 166134397871) ∧
    -Real.log (100000000000 / 166134397871) ≤ (507626901 / 1000000000) := by
  have h := checkLog_sound (w := (66134397871 / 266134397871)) (n := 12)
    (lo := (5076269 / 10000000)) (hi := (507626901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166134397871 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166134397871 / 100000000000) = 1/(100000000000 / 166134397871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8326 : Bounds (5076269 / 10000000) (507626901 / 1000000000) (Real.log (166134397871 / 100000000000)) := by
  have h := reflection_log_8326_neg
  have he : Real.log (166134397871 / 100000000000) = -Real.log (100000000000 / 166134397871) := by
    rw [show ((166134397871 / 100000000000) : ℝ) = ((100000000000 / 166134397871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8327_neg : (222343231 / 1000000000) ≤ -Real.log (1000 / 1249) ∧
    -Real.log (1000 / 1249) ≤ (3474113 / 15625000) := by
  have h := checkLog_sound (w := (249 / 2249)) (n := 12)
    (lo := (222343231 / 1000000000)) (hi := (3474113 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249 / 1000) = 1/(1000 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8327 : Bounds (222343231 / 1000000000) (3474113 / 15625000) (Real.log (1249 / 1000)) := by
  have h := reflection_log_8327_neg
  have he : Real.log (1249 / 1000) = -Real.log (1000 / 1249) := by
    rw [show ((1249 / 1000) : ℝ) = ((1000 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8328_neg : (286349627 / 1000000000) ≤ -Real.log (751 / 1000) ∧
    -Real.log (751 / 1000) ≤ (71587407 / 250000000) := by
  have h := checkLog_sound (w := (249 / 1751)) (n := 12)
    (lo := (286349627 / 1000000000)) (hi := (71587407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 751) = 1/(751 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8328 : Bounds (-71587407 / 250000000) (-286349627 / 1000000000) (Real.log (751 / 1000)) := by
  have h := reflection_log_8328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8329_neg : (248969 / 1000000000) ≤ -Real.log (1000000 / 1000249) ∧
    -Real.log (1000000 / 1000249) ≤ (24897 / 100000000) := by
  have h := checkLog_sound (w := (249 / 2000249)) (n := 12)
    (lo := (248969 / 1000000000)) (hi := (24897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000249 / 1000000) = 1/(1000000 / 1000249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8329 : Bounds (248969 / 1000000000) (24897 / 100000000) (Real.log (1000249 / 1000000)) := by
  have h := reflection_log_8329_neg
  have he : Real.log (1000249 / 1000000) = -Real.log (1000000 / 1000249) := by
    rw [show ((1000249 / 1000000) : ℝ) = ((1000000 / 1000249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8330_neg : (249031 / 1000000000) ≤ -Real.log (999751 / 1000000) ∧
    -Real.log (999751 / 1000000) ≤ (31129 / 125000000) := by
  have h := checkLog_sound (w := (249 / 1999751)) (n := 12)
    (lo := (249031 / 1000000000)) (hi := (31129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999751) = 1/(999751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8330 : Bounds (-31129 / 125000000) (-249031 / 1000000000) (Real.log (999751 / 1000000)) := by
  have h := reflection_log_8330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8331_neg : (59129683 / 500000000) ≤ -Real.log (31250 / 35173) ∧
    -Real.log (31250 / 35173) ≤ (118259367 / 1000000000) := by
  have h := checkLog_sound (w := (3923 / 66423)) (n := 12)
    (lo := (59129683 / 500000000)) (hi := (118259367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35173 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35173 / 31250) = 1/(31250 / 35173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8331 : Bounds (59129683 / 500000000) (118259367 / 1000000000) (Real.log (35173 / 31250)) := by
  have h := reflection_log_8331_neg
  have he : Real.log (35173 / 31250) = -Real.log (31250 / 35173) := by
    rw [show ((35173 / 31250) : ℝ) = ((31250 / 35173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8332_neg : (134144151 / 1000000000) ≤ -Real.log (27327 / 31250) ∧
    -Real.log (27327 / 31250) ≤ (16768019 / 125000000) := by
  have h := checkLog_sound (w := (3923 / 58577)) (n := 12)
    (lo := (134144151 / 1000000000)) (hi := (16768019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27327) = 1/(27327 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8332 : Bounds (-16768019 / 125000000) (-134144151 / 1000000000) (Real.log (27327 / 31250)) := by
  have h := reflection_log_8332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8333_neg : (118707941 / 1000000000) ≤ -Real.log (1000000 / 1126041) ∧
    -Real.log (1000000 / 1126041) ≤ (59353971 / 500000000) := by
  have h := checkLog_sound (w := (126041 / 2126041)) (n := 12)
    (lo := (118707941 / 1000000000)) (hi := (59353971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126041 / 1000000) = 1/(1000000 / 1126041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8333 : Bounds (118707941 / 1000000000) (59353971 / 500000000) (Real.log (1126041 / 1000000)) := by
  have h := reflection_log_8333_neg
  have he : Real.log (1126041 / 1000000) = -Real.log (1000000 / 1126041) := by
    rw [show ((1126041 / 1000000) : ℝ) = ((1000000 / 1126041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8334_neg : (26944363 / 200000000) ≤ -Real.log (873959 / 1000000) ∧
    -Real.log (873959 / 1000000) ≤ (16840227 / 125000000) := by
  have h := checkLog_sound (w := (126041 / 1873959)) (n := 12)
    (lo := (26944363 / 200000000)) (hi := (16840227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873959) = 1/(873959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8334 : Bounds (-16840227 / 125000000) (-26944363 / 200000000) (Real.log (873959 / 1000000)) := by
  have h := reflection_log_8334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8335_neg : (8006937 / 500000000) ≤ -Real.log (984113666319 / 1000000000000) ∧
    -Real.log (984113666319 / 1000000000000) ≤ (128111 / 8000000) := by
  have h := checkLog_sound (w := (15886333681 / 1984113666319)) (n := 12)
    (lo := (8006937 / 500000000)) (hi := (128111 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984113666319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984113666319) = 1/(984113666319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8335 : Bounds (-128111 / 8000000) (-8006937 / 500000000) (Real.log (984113666319 / 1000000000000)) := by
  have h := reflection_log_8335_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8336_neg : (3176957 / 200000000) ≤ -Real.log (961172571 / 976562500) ∧
    -Real.log (961172571 / 976562500) ≤ (7942393 / 500000000) := by
  have h := checkLog_sound (w := (15389929 / 1937735071)) (n := 12)
    (lo := (3176957 / 200000000)) (hi := (7942393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 961172571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 961172571) = 1/(961172571 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8336 : Bounds (-7942393 / 500000000) (-3176957 / 200000000) (Real.log (961172571 / 976562500)) := by
  have h := reflection_log_8336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8337_neg : (126201759 / 500000000) ≤ -Real.log (250000000000 / 321778826801) ∧
    -Real.log (250000000000 / 321778826801) ≤ (252403519 / 1000000000) := by
  have h := checkLog_sound (w := (71778826801 / 571778826801)) (n := 12)
    (lo := (126201759 / 500000000)) (hi := (252403519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321778826801 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321778826801 / 250000000000) = 1/(250000000000 / 321778826801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8337 : Bounds (126201759 / 500000000) (252403519 / 1000000000) (Real.log (321778826801 / 250000000000)) := by
  have h := reflection_log_8337_neg
  have he : Real.log (321778826801 / 250000000000) = -Real.log (250000000000 / 321778826801) := by
    rw [show ((321778826801 / 250000000000) : ℝ) = ((250000000000 / 321778826801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8338_neg : (63357439 / 250000000) ≤ -Real.log (500000000000 / 644218435877) ∧
    -Real.log (500000000000 / 644218435877) ≤ (253429757 / 1000000000) := by
  have h := checkLog_sound (w := (144218435877 / 1144218435877)) (n := 12)
    (lo := (63357439 / 250000000)) (hi := (253429757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644218435877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644218435877 / 500000000000) = 1/(500000000000 / 644218435877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8338 : Bounds (63357439 / 250000000) (253429757 / 1000000000) (Real.log (644218435877 / 500000000000)) := by
  have h := reflection_log_8338_neg
  have he : Real.log (644218435877 / 500000000000) = -Real.log (500000000000 / 644218435877) := by
    rw [show ((644218435877 / 500000000000) : ℝ) = ((500000000000 / 644218435877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8339_neg : (5076269 / 10000000) ≤ -Real.log (250000000000 / 415335994677) ∧
    -Real.log (250000000000 / 415335994677) ≤ (507626901 / 1000000000) := by
  have h := checkLog_sound (w := (165335994677 / 665335994677)) (n := 12)
    (lo := (5076269 / 10000000)) (hi := (507626901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415335994677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415335994677 / 250000000000) = 1/(250000000000 / 415335994677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8339 : Bounds (5076269 / 10000000) (507626901 / 1000000000) (Real.log (415335994677 / 250000000000)) := by
  have h := reflection_log_8339_neg
  have he : Real.log (415335994677 / 250000000000) = -Real.log (250000000000 / 415335994677) := by
    rw [show ((415335994677 / 250000000000) : ℝ) = ((250000000000 / 415335994677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8340_neg : (254346429 / 500000000) ≤ -Real.log (50000000000 / 83155792277) ∧
    -Real.log (50000000000 / 83155792277) ≤ (508692859 / 1000000000) := by
  have h := checkLog_sound (w := (33155792277 / 133155792277)) (n := 12)
    (lo := (254346429 / 500000000)) (hi := (508692859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83155792277 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83155792277 / 50000000000) = 1/(50000000000 / 83155792277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8340 : Bounds (254346429 / 500000000) (508692859 / 1000000000) (Real.log (83155792277 / 50000000000)) := by
  have h := reflection_log_8340_neg
  have he : Real.log (83155792277 / 50000000000) = -Real.log (50000000000 / 83155792277) := by
    rw [show ((83155792277 / 50000000000) : ℝ) = ((50000000000 / 83155792277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8341_neg : (222743471 / 1000000000) ≤ -Real.log (2000 / 2499) ∧
    -Real.log (2000 / 2499) ≤ (13921467 / 62500000) := by
  have h := checkLog_sound (w := (499 / 4499)) (n := 12)
    (lo := (222743471 / 1000000000)) (hi := (13921467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2000) = 1/(2000 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8341 : Bounds (222743471 / 1000000000) (13921467 / 62500000) (Real.log (2499 / 2000)) := by
  have h := reflection_log_8341_neg
  have he : Real.log (2499 / 2000) = -Real.log (2000 / 2499) := by
    rw [show ((2499 / 2000) : ℝ) = ((2000 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8342_neg : (287015627 / 1000000000) ≤ -Real.log (1501 / 2000) ∧
    -Real.log (1501 / 2000) ≤ (71753907 / 250000000) := by
  have h := checkLog_sound (w := (499 / 3501)) (n := 12)
    (lo := (287015627 / 1000000000)) (hi := (71753907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1501) = 1/(1501 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8342 : Bounds (-71753907 / 250000000) (-287015627 / 1000000000) (Real.log (1501 / 2000)) := by
  have h := reflection_log_8342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8343_neg : (62367 / 250000000) ≤ -Real.log (2000000 / 2000499) ∧
    -Real.log (2000000 / 2000499) ≤ (249469 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4000499)) (n := 12)
    (lo := (62367 / 250000000)) (hi := (249469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000499 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000499 / 2000000) = 1/(2000000 / 2000499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8343 : Bounds (62367 / 250000000) (249469 / 1000000000) (Real.log (2000499 / 2000000)) := by
  have h := reflection_log_8343_neg
  have he : Real.log (2000499 / 2000000) = -Real.log (2000000 / 2000499) := by
    rw [show ((2000499 / 2000000) : ℝ) = ((2000000 / 2000499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8344_neg : (249531 / 1000000000) ≤ -Real.log (1999501 / 2000000) ∧
    -Real.log (1999501 / 2000000) ≤ (62383 / 250000000) := by
  have h := checkLog_sound (w := (499 / 3999501)) (n := 12)
    (lo := (249531 / 1000000000)) (hi := (62383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999501) = 1/(1999501 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8344 : Bounds (-62383 / 250000000) (-249531 / 1000000000) (Real.log (1999501 / 2000000)) := by
  have h := reflection_log_8344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8345_neg : (29622141 / 250000000) ≤ -Real.log (500000 / 562897) ∧
    -Real.log (500000 / 562897) ≤ (23697713 / 200000000) := by
  have h := checkLog_sound (w := (62897 / 1062897)) (n := 12)
    (lo := (29622141 / 250000000)) (hi := (23697713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562897 / 500000) = 1/(500000 / 562897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8345 : Bounds (29622141 / 250000000) (23697713 / 200000000) (Real.log (562897 / 500000)) := by
  have h := reflection_log_8345_neg
  have he : Real.log (562897 / 500000) = -Real.log (500000 / 562897) := by
    rw [show ((562897 / 500000) : ℝ) = ((500000 / 562897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8346_neg : (134439233 / 1000000000) ≤ -Real.log (437103 / 500000) ∧
    -Real.log (437103 / 500000) ≤ (67219617 / 500000000) := by
  have h := checkLog_sound (w := (62897 / 937103)) (n := 12)
    (lo := (134439233 / 1000000000)) (hi := (67219617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437103) = 1/(437103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8346 : Bounds (-67219617 / 500000000) (-134439233 / 1000000000) (Real.log (437103 / 500000)) := by
  have h := reflection_log_8346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8347_neg : (29734481 / 250000000) ≤ -Real.log (10000 / 11263) ∧
    -Real.log (10000 / 11263) ≤ (4757517 / 40000000) := by
  have h := checkLog_sound (w := (1263 / 21263)) (n := 12)
    (lo := (29734481 / 250000000)) (hi := (4757517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11263 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11263 / 10000) = 1/(10000 / 11263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8347 : Bounds (29734481 / 250000000) (4757517 / 40000000) (Real.log (11263 / 10000)) := by
  have h := reflection_log_8347_neg
  have he : Real.log (11263 / 10000) = -Real.log (10000 / 11263) := by
    rw [show ((11263 / 10000) : ℝ) = ((10000 / 11263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8348_neg : (135018211 / 1000000000) ≤ -Real.log (8737 / 10000) ∧
    -Real.log (8737 / 10000) ≤ (33754553 / 250000000) := by
  have h := checkLog_sound (w := (1263 / 18737)) (n := 12)
    (lo := (135018211 / 1000000000)) (hi := (33754553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8737) = 1/(8737 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8348 : Bounds (-33754553 / 250000000) (-135018211 / 1000000000) (Real.log (8737 / 10000)) := by
  have h := reflection_log_8348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8349_neg : (16080287 / 1000000000) ≤ -Real.log (98404831 / 100000000) ∧
    -Real.log (98404831 / 100000000) ≤ (502509 / 31250000) := by
  have h := checkLog_sound (w := (1595169 / 198404831)) (n := 12)
    (lo := (16080287 / 1000000000)) (hi := (502509 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98404831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98404831) = 1/(98404831 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8349 : Bounds (-502509 / 31250000) (-16080287 / 1000000000) (Real.log (98404831 / 100000000)) := by
  have h := reflection_log_8349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8350_neg : (3987667 / 250000000) ≤ -Real.log (246043967391 / 250000000000) ∧
    -Real.log (246043967391 / 250000000000) ≤ (15950669 / 1000000000) := by
  have h := checkLog_sound (w := (3956032609 / 496043967391)) (n := 12)
    (lo := (3987667 / 250000000)) (hi := (15950669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246043967391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246043967391) = 1/(246043967391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8350 : Bounds (-15950669 / 1000000000) (-3987667 / 250000000) (Real.log (246043967391 / 250000000000)) := by
  have h := reflection_log_8350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8351_neg : (252927797 / 1000000000) ≤ -Real.log (100000000000 / 128779029199) ∧
    -Real.log (100000000000 / 128779029199) ≤ (126463899 / 500000000) := by
  have h := checkLog_sound (w := (28779029199 / 228779029199)) (n := 12)
    (lo := (252927797 / 1000000000)) (hi := (126463899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128779029199 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128779029199 / 100000000000) = 1/(100000000000 / 128779029199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8351 : Bounds (252927797 / 1000000000) (126463899 / 500000000) (Real.log (128779029199 / 100000000000)) := by
  have h := reflection_log_8351_neg
  have he : Real.log (128779029199 / 100000000000) = -Real.log (100000000000 / 128779029199) := by
    rw [show ((128779029199 / 100000000000) : ℝ) = ((100000000000 / 128779029199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8352_neg : (50791227 / 200000000) ≤ -Real.log (500000000000 / 644557628477) ∧
    -Real.log (500000000000 / 644557628477) ≤ (31744517 / 125000000) := by
  have h := checkLog_sound (w := (144557628477 / 1144557628477)) (n := 12)
    (lo := (50791227 / 200000000)) (hi := (31744517 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644557628477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644557628477 / 500000000000) = 1/(500000000000 / 644557628477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8352 : Bounds (50791227 / 200000000) (31744517 / 125000000) (Real.log (644557628477 / 500000000000)) := by
  have h := reflection_log_8352_neg
  have he : Real.log (644557628477 / 500000000000) = -Real.log (500000000000 / 644557628477) := by
    rw [show ((644557628477 / 500000000000) : ℝ) = ((500000000000 / 644557628477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8353_neg : (254346429 / 500000000) ≤ -Real.log (500000000000 / 831557922769) ∧
    -Real.log (500000000000 / 831557922769) ≤ (508692859 / 1000000000) := by
  have h := checkLog_sound (w := (331557922769 / 1331557922769)) (n := 12)
    (lo := (254346429 / 500000000)) (hi := (508692859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831557922769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831557922769 / 500000000000) = 1/(500000000000 / 831557922769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8353 : Bounds (254346429 / 500000000) (508692859 / 1000000000) (Real.log (831557922769 / 500000000000)) := by
  have h := reflection_log_8353_neg
  have he : Real.log (831557922769 / 500000000000) = -Real.log (500000000000 / 831557922769) := by
    rw [show ((831557922769 / 500000000000) : ℝ) = ((500000000000 / 831557922769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8354_neg : (509759099 / 1000000000) ≤ -Real.log (500000000000 / 832445036643) ∧
    -Real.log (500000000000 / 832445036643) ≤ (5097591 / 10000000) := by
  have h := checkLog_sound (w := (332445036643 / 1332445036643)) (n := 12)
    (lo := (509759099 / 1000000000)) (hi := (5097591 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832445036643 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832445036643 / 500000000000) = 1/(500000000000 / 832445036643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8354 : Bounds (509759099 / 1000000000) (5097591 / 10000000) (Real.log (832445036643 / 500000000000)) := by
  have h := reflection_log_8354_neg
  have he : Real.log (832445036643 / 500000000000) = -Real.log (500000000000 / 832445036643) := by
    rw [show ((832445036643 / 500000000000) : ℝ) = ((500000000000 / 832445036643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8355_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8355 : Bounds (223143551 / 1000000000) (1743309 / 7812500) (Real.log (5 / 4)) := by
  have h := reflection_log_8355_neg
  have he : Real.log (5 / 4) = -Real.log (4 / 5) := by
    rw [show ((5 / 4) : ℝ) = ((4 / 5) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8356_neg : (35960259 / 125000000) ≤ -Real.log (3 / 4) ∧
    -Real.log (3 / 4) ≤ (287682073 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4 / 3) = 1/(3 / 4) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8356 : Bounds (-287682073 / 1000000000) (-35960259 / 125000000) (Real.log (3 / 4)) := by
  have h := reflection_log_8356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8357_neg : (15623 / 62500000) ≤ -Real.log (4000 / 4001) ∧
    -Real.log (4000 / 4001) ≤ (249969 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 8001)) (n := 12)
    (lo := (15623 / 62500000)) (hi := (249969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 4000) = 1/(4000 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8357 : Bounds (15623 / 62500000) (249969 / 1000000000) (Real.log (4001 / 4000)) := by
  have h := reflection_log_8357_neg
  have he : Real.log (4001 / 4000) = -Real.log (4000 / 4001) := by
    rw [show ((4001 / 4000) : ℝ) = ((4000 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8358_neg : (250031 / 1000000000) ≤ -Real.log (3999 / 4000) ∧
    -Real.log (3999 / 4000) ≤ (15627 / 62500000) := by
  have h := checkLog_sound (w := (1 / 7999)) (n := 12)
    (lo := (250031 / 1000000000)) (hi := (15627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3999) = 1/(3999 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8358 : Bounds (-15627 / 62500000) (-250031 / 1000000000) (Real.log (3999 / 4000)) := by
  have h := reflection_log_8358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8359_neg : (118718597 / 1000000000) ≤ -Real.log (1000000 / 1126053) ∧
    -Real.log (1000000 / 1126053) ≤ (59359299 / 500000000) := by
  have h := checkLog_sound (w := (126053 / 2126053)) (n := 12)
    (lo := (118718597 / 1000000000)) (hi := (59359299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126053 / 1000000) = 1/(1000000 / 1126053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8359 : Bounds (118718597 / 1000000000) (59359299 / 500000000) (Real.log (1126053 / 1000000)) := by
  have h := reflection_log_8359_neg
  have he : Real.log (1126053 / 1000000) = -Real.log (1000000 / 1126053) := by
    rw [show ((1126053 / 1000000) : ℝ) = ((1000000 / 1126053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8360_neg : (26947109 / 200000000) ≤ -Real.log (873947 / 1000000) ∧
    -Real.log (873947 / 1000000) ≤ (67367773 / 500000000) := by
  have h := checkLog_sound (w := (126053 / 1873947)) (n := 12)
    (lo := (26947109 / 200000000)) (hi := (67367773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873947) = 1/(873947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8360 : Bounds (-67367773 / 500000000) (-26947109 / 200000000) (Real.log (873947 / 1000000)) := by
  have h := reflection_log_8360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8361_neg : (59583927 / 500000000) ≤ -Real.log (1000000 / 1126559) ∧
    -Real.log (1000000 / 1126559) ≤ (23833571 / 200000000) := by
  have h := checkLog_sound (w := (126559 / 2126559)) (n := 12)
    (lo := (59583927 / 500000000)) (hi := (23833571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126559 / 1000000) = 1/(1000000 / 1126559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8361 : Bounds (59583927 / 500000000) (23833571 / 200000000) (Real.log (1126559 / 1000000)) := by
  have h := reflection_log_8361_neg
  have he : Real.log (1126559 / 1000000) = -Real.log (1000000 / 1126559) := by
    rw [show ((1126559 / 1000000) : ℝ) = ((1000000 / 1126559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8362_neg : (16914337 / 125000000) ≤ -Real.log (873441 / 1000000) ∧
    -Real.log (873441 / 1000000) ≤ (135314697 / 1000000000) := by
  have h := checkLog_sound (w := (126559 / 1873441)) (n := 12)
    (lo := (16914337 / 125000000)) (hi := (135314697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873441) = 1/(873441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8362 : Bounds (-135314697 / 1000000000) (-16914337 / 125000000) (Real.log (873441 / 1000000)) := by
  have h := reflection_log_8362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8363_neg : (16146841 / 1000000000) ≤ -Real.log (983982819519 / 1000000000000) ∧
    -Real.log (983982819519 / 1000000000000) ≤ (8073421 / 500000000) := by
  have h := checkLog_sound (w := (16017180481 / 1983982819519)) (n := 12)
    (lo := (16146841 / 1000000000)) (hi := (8073421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983982819519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983982819519) = 1/(983982819519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8363 : Bounds (-8073421 / 500000000) (-16146841 / 1000000000) (Real.log (983982819519 / 1000000000000)) := by
  have h := reflection_log_8363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8364_neg : (4004237 / 250000000) ≤ -Real.log (984110641191 / 1000000000000) ∧
    -Real.log (984110641191 / 1000000000000) ≤ (16016949 / 1000000000) := by
  have h := checkLog_sound (w := (15889358809 / 1984110641191)) (n := 12)
    (lo := (4004237 / 250000000)) (hi := (16016949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984110641191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984110641191) = 1/(984110641191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8364 : Bounds (-16016949 / 1000000000) (-4004237 / 250000000) (Real.log (984110641191 / 1000000000000)) := by
  have h := reflection_log_8364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8365_neg : (253454143 / 1000000000) ≤ -Real.log (500000000000 / 644234146921) ∧
    -Real.log (500000000000 / 644234146921) ≤ (3960221 / 15625000) := by
  have h := checkLog_sound (w := (144234146921 / 1144234146921)) (n := 12)
    (lo := (253454143 / 1000000000)) (hi := (3960221 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644234146921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644234146921 / 500000000000) = 1/(500000000000 / 644234146921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8365 : Bounds (253454143 / 1000000000) (3960221 / 15625000) (Real.log (644234146921 / 500000000000)) := by
  have h := reflection_log_8365_neg
  have he : Real.log (644234146921 / 500000000000) = -Real.log (500000000000 / 644234146921) := by
    rw [show ((644234146921 / 500000000000) : ℝ) = ((500000000000 / 644234146921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8366_neg : (5089651 / 20000000) ≤ -Real.log (250000000000 / 322448511119) ∧
    -Real.log (250000000000 / 322448511119) ≤ (254482551 / 1000000000) := by
  have h := checkLog_sound (w := (72448511119 / 572448511119)) (n := 12)
    (lo := (5089651 / 20000000)) (hi := (254482551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322448511119 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322448511119 / 250000000000) = 1/(250000000000 / 322448511119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8366 : Bounds (5089651 / 20000000) (254482551 / 1000000000) (Real.log (322448511119 / 250000000000)) := by
  have h := reflection_log_8366_neg
  have he : Real.log (322448511119 / 250000000000) = -Real.log (250000000000 / 322448511119) := by
    rw [show ((322448511119 / 250000000000) : ℝ) = ((250000000000 / 322448511119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8367_neg : (509759099 / 1000000000) ≤ -Real.log (250000000000 / 416222518321) ∧
    -Real.log (250000000000 / 416222518321) ≤ (5097591 / 10000000) := by
  have h := checkLog_sound (w := (166222518321 / 666222518321)) (n := 12)
    (lo := (509759099 / 1000000000)) (hi := (5097591 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416222518321 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416222518321 / 250000000000) = 1/(250000000000 / 416222518321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8367 : Bounds (509759099 / 1000000000) (5097591 / 10000000) (Real.log (416222518321 / 250000000000)) := by
  have h := reflection_log_8367_neg
  have he : Real.log (416222518321 / 250000000000) = -Real.log (250000000000 / 416222518321) := by
    rw [show ((416222518321 / 250000000000) : ℝ) = ((250000000000 / 416222518321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8368_neg : (510825623 / 1000000000) ≤ -Real.log (250000000000 / 416666666667) ∧
    -Real.log (250000000000 / 416666666667) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (166666666667 / 666666666667)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416666666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416666666667 / 250000000000) = 1/(250000000000 / 416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8368 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (416666666667 / 250000000000)) := by
  have h := reflection_log_8368_neg
  have he : Real.log (416666666667 / 250000000000) = -Real.log (250000000000 / 416666666667) := by
    rw [show ((416666666667 / 250000000000) : ℝ) = ((250000000000 / 416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8369_neg : (223543471 / 1000000000) ≤ -Real.log (2000 / 2501) ∧
    -Real.log (2000 / 2501) ≤ (13971467 / 62500000) := by
  have h := checkLog_sound (w := (501 / 4501)) (n := 12)
    (lo := (223543471 / 1000000000)) (hi := (13971467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2501 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2501 / 2000) = 1/(2000 / 2501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8369 : Bounds (223543471 / 1000000000) (13971467 / 62500000) (Real.log (2501 / 2000)) := by
  have h := reflection_log_8369_neg
  have he : Real.log (2501 / 2000) = -Real.log (2000 / 2501) := by
    rw [show ((2501 / 2000) : ℝ) = ((2000 / 2501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8370_neg : (288348961 / 1000000000) ≤ -Real.log (1499 / 2000) ∧
    -Real.log (1499 / 2000) ≤ (144174481 / 500000000) := by
  have h := checkLog_sound (w := (501 / 3499)) (n := 12)
    (lo := (288348961 / 1000000000)) (hi := (144174481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1499) = 1/(1499 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8370 : Bounds (-144174481 / 500000000) (-288348961 / 1000000000) (Real.log (1499 / 2000)) := by
  have h := reflection_log_8370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8371_neg : (62617 / 250000000) ≤ -Real.log (2000000 / 2000501) ∧
    -Real.log (2000000 / 2000501) ≤ (250469 / 1000000000) := by
  have h := checkLog_sound (w := (501 / 4000501)) (n := 12)
    (lo := (62617 / 250000000)) (hi := (250469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000501 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000501 / 2000000) = 1/(2000000 / 2000501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8371 : Bounds (62617 / 250000000) (250469 / 1000000000) (Real.log (2000501 / 2000000)) := by
  have h := reflection_log_8371_neg
  have he : Real.log (2000501 / 2000000) = -Real.log (2000000 / 2000501) := by
    rw [show ((2000501 / 2000000) : ℝ) = ((2000000 / 2000501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8372_neg : (250531 / 1000000000) ≤ -Real.log (1999499 / 2000000) ∧
    -Real.log (1999499 / 2000000) ≤ (62633 / 250000000) := by
  have h := checkLog_sound (w := (501 / 3999499)) (n := 12)
    (lo := (250531 / 1000000000)) (hi := (62633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999499) = 1/(1999499 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8372 : Bounds (-62633 / 250000000) (-250531 / 1000000000) (Real.log (1999499 / 2000000)) := by
  have h := reflection_log_8372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8373_neg : (11894769 / 100000000) ≤ -Real.log (1000000 / 1126311) ∧
    -Real.log (1000000 / 1126311) ≤ (118947691 / 1000000000) := by
  have h := checkLog_sound (w := (126311 / 2126311)) (n := 12)
    (lo := (11894769 / 100000000)) (hi := (118947691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126311 / 1000000) = 1/(1000000 / 1126311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8373 : Bounds (11894769 / 100000000) (118947691 / 1000000000) (Real.log (1126311 / 1000000)) := by
  have h := reflection_log_8373_neg
  have he : Real.log (1126311 / 1000000) = -Real.log (1000000 / 1126311) := by
    rw [show ((1126311 / 1000000) : ℝ) = ((1000000 / 1126311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8374_neg : (135030801 / 1000000000) ≤ -Real.log (873689 / 1000000) ∧
    -Real.log (873689 / 1000000) ≤ (67515401 / 500000000) := by
  have h := checkLog_sound (w := (126311 / 1873689)) (n := 12)
    (lo := (135030801 / 1000000000)) (hi := (67515401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873689) = 1/(873689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8374 : Bounds (-67515401 / 500000000) (-135030801 / 1000000000) (Real.log (873689 / 1000000)) := by
  have h := reflection_log_8374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8375_neg : (119397731 / 1000000000) ≤ -Real.log (500000 / 563409) ∧
    -Real.log (500000 / 563409) ≤ (29849433 / 250000000) := by
  have h := checkLog_sound (w := (63409 / 1063409)) (n := 12)
    (lo := (119397731 / 1000000000)) (hi := (29849433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563409 / 500000) = 1/(500000 / 563409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8375 : Bounds (119397731 / 1000000000) (29849433 / 250000000) (Real.log (563409 / 500000)) := by
  have h := reflection_log_8375_neg
  have he : Real.log (563409 / 500000) = -Real.log (500000 / 563409) := by
    rw [show ((563409 / 500000) : ℝ) = ((500000 / 563409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8376_neg : (33902817 / 250000000) ≤ -Real.log (436591 / 500000) ∧
    -Real.log (436591 / 500000) ≤ (135611269 / 1000000000) := by
  have h := checkLog_sound (w := (63409 / 936591)) (n := 12)
    (lo := (33902817 / 250000000)) (hi := (135611269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436591) = 1/(436591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8376 : Bounds (-135611269 / 1000000000) (-33902817 / 250000000) (Real.log (436591 / 500000)) := by
  have h := reflection_log_8376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8377_neg : (16213537 / 1000000000) ≤ -Real.log (245979298719 / 250000000000) ∧
    -Real.log (245979298719 / 250000000000) ≤ (8106769 / 500000000) := by
  have h := checkLog_sound (w := (4020701281 / 495979298719)) (n := 12)
    (lo := (16213537 / 1000000000)) (hi := (8106769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245979298719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245979298719) = 1/(245979298719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8377 : Bounds (-8106769 / 500000000) (-16213537 / 1000000000) (Real.log (245979298719 / 250000000000)) := by
  have h := reflection_log_8377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8378_neg : (16083111 / 1000000000) ≤ -Real.log (984045531279 / 1000000000000) ∧
    -Real.log (984045531279 / 1000000000000) ≤ (2010389 / 125000000) := by
  have h := checkLog_sound (w := (15954468721 / 1984045531279)) (n := 12)
    (lo := (16083111 / 1000000000)) (hi := (2010389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984045531279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984045531279) = 1/(984045531279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8378 : Bounds (-2010389 / 125000000) (-16083111 / 1000000000) (Real.log (984045531279 / 1000000000000)) := by
  have h := reflection_log_8378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8379_neg : (63494623 / 250000000) ≤ -Real.log (500000000000 / 644572038791) ∧
    -Real.log (500000000000 / 644572038791) ≤ (253978493 / 1000000000) := by
  have h := checkLog_sound (w := (144572038791 / 1144572038791)) (n := 12)
    (lo := (63494623 / 250000000)) (hi := (253978493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644572038791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644572038791 / 500000000000) = 1/(500000000000 / 644572038791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8379 : Bounds (63494623 / 250000000) (253978493 / 1000000000) (Real.log (644572038791 / 500000000000)) := by
  have h := reflection_log_8379_neg
  have he : Real.log (644572038791 / 500000000000) = -Real.log (500000000000 / 644572038791) := by
    rw [show ((644572038791 / 500000000000) : ℝ) = ((500000000000 / 644572038791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8380_neg : (255008999 / 1000000000) ≤ -Real.log (250000000000 / 322618308669) ∧
    -Real.log (250000000000 / 322618308669) ≤ (255009 / 1000000) := by
  have h := checkLog_sound (w := (72618308669 / 572618308669)) (n := 12)
    (lo := (255008999 / 1000000000)) (hi := (255009 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322618308669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322618308669 / 250000000000) = 1/(250000000000 / 322618308669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8380 : Bounds (255008999 / 1000000000) (255009 / 1000000) (Real.log (322618308669 / 250000000000)) := by
  have h := reflection_log_8380_neg
  have he : Real.log (322618308669 / 250000000000) = -Real.log (250000000000 / 322618308669) := by
    rw [show ((322618308669 / 250000000000) : ℝ) = ((250000000000 / 322618308669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8381_neg : (510825623 / 1000000000) ≤ -Real.log (500000000000 / 833333333333) ∧
    -Real.log (500000000000 / 833333333333) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (333333333333 / 1333333333333)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833333333333 / 500000000000) = 1/(500000000000 / 833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8381 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (833333333333 / 500000000000)) := by
  have h := reflection_log_8381_neg
  have he : Real.log (833333333333 / 500000000000) = -Real.log (500000000000 / 833333333333) := by
    rw [show ((833333333333 / 500000000000) : ℝ) = ((500000000000 / 833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8382_neg : (31993277 / 62500000) ≤ -Real.log (500000000000 / 834222815211) ∧
    -Real.log (500000000000 / 834222815211) ≤ (511892433 / 1000000000) := by
  have h := checkLog_sound (w := (334222815211 / 1334222815211)) (n := 12)
    (lo := (31993277 / 62500000)) (hi := (511892433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834222815211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834222815211 / 500000000000) = 1/(500000000000 / 834222815211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8382 : Bounds (31993277 / 62500000) (511892433 / 1000000000) (Real.log (834222815211 / 500000000000)) := by
  have h := reflection_log_8382_neg
  have he : Real.log (834222815211 / 500000000000) = -Real.log (500000000000 / 834222815211) := by
    rw [show ((834222815211 / 500000000000) : ℝ) = ((500000000000 / 834222815211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8383_neg : (223943231 / 1000000000) ≤ -Real.log (1000 / 1251) ∧
    -Real.log (1000 / 1251) ≤ (3499113 / 15625000) := by
  have h := checkLog_sound (w := (251 / 2251)) (n := 12)
    (lo := (223943231 / 1000000000)) (hi := (3499113 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1000) = 1/(1000 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8383 : Bounds (223943231 / 1000000000) (3499113 / 15625000) (Real.log (1251 / 1000)) := by
  have h := reflection_log_8383_neg
  have he : Real.log (1251 / 1000) = -Real.log (1000 / 1251) := by
    rw [show ((1251 / 1000) : ℝ) = ((1000 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


