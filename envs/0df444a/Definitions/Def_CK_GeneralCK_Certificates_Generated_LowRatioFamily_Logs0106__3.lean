-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0106__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0106__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T02:20:46.690369+00:00
-- url     : https://prove2.me/theorems/0792b329-fe09-4cb7-947d-e9cda519b28d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0106 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0107, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0106 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0107, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0108)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0106 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0107, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0108)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0106 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0107, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0108) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0106 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0107, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0108).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0106 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6784_neg : (200498979 / 1000000000) ≤ -Real.log (500000000000 / 611006182749) ∧
    -Real.log (500000000000 / 611006182749) ≤ (10024949 / 50000000) := by
  have h := checkLog_sound (w := (111006182749 / 1111006182749)) (n := 12)
    (lo := (200498979 / 1000000000)) (hi := (10024949 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611006182749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611006182749 / 500000000000) = 1/(500000000000 / 611006182749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6784 : Bounds (200498979 / 1000000000) (10024949 / 50000000) (Real.log (611006182749 / 500000000000)) := by
  have h := reflection_log_6784_neg
  have he : Real.log (611006182749 / 500000000000) = -Real.log (500000000000 / 611006182749) := by
    rw [show ((611006182749 / 500000000000) : ℝ) = ((500000000000 / 611006182749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6785_neg : (100502017 / 500000000) ≤ -Real.log (62500000000 / 76414356521) ∧
    -Real.log (62500000000 / 76414356521) ≤ (40200807 / 200000000) := by
  have h := checkLog_sound (w := (13914356521 / 138914356521)) (n := 12)
    (lo := (100502017 / 500000000)) (hi := (40200807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76414356521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76414356521 / 62500000000) = 1/(62500000000 / 76414356521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6785 : Bounds (100502017 / 500000000) (40200807 / 200000000) (Real.log (76414356521 / 62500000000)) := by
  have h := reflection_log_6785_neg
  have he : Real.log (76414356521 / 62500000000) = -Real.log (62500000000 / 76414356521) := by
    rw [show ((76414356521 / 62500000000) : ℝ) = ((62500000000 / 76414356521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6786_neg : (402549289 / 1000000000) ≤ -Real.log (500000000000 / 747816321437) ∧
    -Real.log (500000000000 / 747816321437) ≤ (40254929 / 100000000) := by
  have h := checkLog_sound (w := (247816321437 / 1247816321437)) (n := 12)
    (lo := (402549289 / 1000000000)) (hi := (40254929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747816321437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747816321437 / 500000000000) = 1/(500000000000 / 747816321437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6786 : Bounds (402549289 / 1000000000) (40254929 / 100000000) (Real.log (747816321437 / 500000000000)) := by
  have h := reflection_log_6786_neg
  have he : Real.log (747816321437 / 500000000000) = -Real.log (500000000000 / 747816321437) := by
    rw [show ((747816321437 / 500000000000) : ℝ) = ((500000000000 / 747816321437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6787_neg : (201378753 / 500000000) ≤ -Real.log (500000000000 / 747972045427) ∧
    -Real.log (500000000000 / 747972045427) ≤ (402757507 / 1000000000) := by
  have h := checkLog_sound (w := (247972045427 / 1247972045427)) (n := 12)
    (lo := (201378753 / 500000000)) (hi := (402757507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747972045427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747972045427 / 500000000000) = 1/(500000000000 / 747972045427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6787 : Bounds (201378753 / 500000000) (402757507 / 1000000000) (Real.log (747972045427 / 500000000000)) := by
  have h := reflection_log_6787_neg
  have he : Real.log (747972045427 / 500000000000) = -Real.log (500000000000 / 747972045427) := by
    rw [show ((747972045427 / 500000000000) : ℝ) = ((500000000000 / 747972045427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6788_neg : (5666283 / 31250000) ≤ -Real.log (2500 / 2997) ∧
    -Real.log (2500 / 2997) ≤ (181321057 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 5497)) (n := 12)
    (lo := (5666283 / 31250000)) (hi := (181321057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 2500) = 1/(2500 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6788 : Bounds (5666283 / 31250000) (181321057 / 1000000000) (Real.log (2997 / 2500)) := by
  have h := reflection_log_6788_neg
  have he : Real.log (2997 / 2500) = -Real.log (2500 / 2997) := by
    rw [show ((2997 / 2500) : ℝ) = ((2500 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6789_neg : (8865787 / 40000000) ≤ -Real.log (2003 / 2500) ∧
    -Real.log (2003 / 2500) ≤ (55411169 / 250000000) := by
  have h := checkLog_sound (w := (497 / 4503)) (n := 12)
    (lo := (8865787 / 40000000)) (hi := (55411169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2003) = 1/(2003 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6789 : Bounds (-55411169 / 250000000) (-8865787 / 40000000) (Real.log (2003 / 2500)) := by
  have h := reflection_log_6789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6790_neg : (9939 / 50000000) ≤ -Real.log (2500000 / 2500497) ∧
    -Real.log (2500000 / 2500497) ≤ (198781 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 5000497)) (n := 12)
    (lo := (9939 / 50000000)) (hi := (198781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500497 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500497 / 2500000) = 1/(2500000 / 2500497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6790 : Bounds (9939 / 50000000) (198781 / 1000000000) (Real.log (2500497 / 2500000)) := by
  have h := reflection_log_6790_neg
  have he : Real.log (2500497 / 2500000) = -Real.log (2500000 / 2500497) := by
    rw [show ((2500497 / 2500000) : ℝ) = ((2500000 / 2500497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6791_neg : (198819 / 1000000000) ≤ -Real.log (2499503 / 2500000) ∧
    -Real.log (2499503 / 2500000) ≤ (9941 / 50000000) := by
  have h := checkLog_sound (w := (497 / 4999503)) (n := 12)
    (lo := (198819 / 1000000000)) (hi := (9941 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499503) = 1/(2499503 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6791 : Bounds (-9941 / 50000000) (-198819 / 1000000000) (Real.log (2499503 / 2500000)) := by
  have h := reflection_log_6791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6792_neg : (95280179 / 1000000000) ≤ -Real.log (1000000 / 1099967) ∧
    -Real.log (1000000 / 1099967) ≤ (4764009 / 50000000) := by
  have h := checkLog_sound (w := (99967 / 2099967)) (n := 12)
    (lo := (95280179 / 1000000000)) (hi := (4764009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099967 / 1000000) = 1/(1000000 / 1099967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6792 : Bounds (95280179 / 1000000000) (4764009 / 50000000) (Real.log (1099967 / 1000000)) := by
  have h := reflection_log_6792_neg
  have he : Real.log (1099967 / 1000000) = -Real.log (1000000 / 1099967) := by
    rw [show ((1099967 / 1000000) : ℝ) = ((1000000 / 1099967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6793_neg : (105323849 / 1000000000) ≤ -Real.log (900033 / 1000000) ∧
    -Real.log (900033 / 1000000) ≤ (2106477 / 20000000) := by
  have h := checkLog_sound (w := (99967 / 1900033)) (n := 12)
    (lo := (105323849 / 1000000000)) (hi := (2106477 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900033) = 1/(900033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6793 : Bounds (-2106477 / 20000000) (-105323849 / 1000000000) (Real.log (900033 / 1000000)) := by
  have h := reflection_log_6793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6794_neg : (23876631 / 250000000) ≤ -Real.log (125000 / 137527) ∧
    -Real.log (125000 / 137527) ≤ (3820261 / 40000000) := by
  have h := checkLog_sound (w := (12527 / 262527)) (n := 12)
    (lo := (23876631 / 250000000)) (hi := (3820261 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137527 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137527 / 125000) = 1/(125000 / 137527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6794 : Bounds (23876631 / 250000000) (3820261 / 40000000) (Real.log (137527 / 125000)) := by
  have h := reflection_log_6794_neg
  have he : Real.log (137527 / 125000) = -Real.log (125000 / 137527) := by
    rw [show ((137527 / 125000) : ℝ) = ((125000 / 137527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6795_neg : (3300017 / 31250000) ≤ -Real.log (112473 / 125000) ∧
    -Real.log (112473 / 125000) ≤ (21120109 / 200000000) := by
  have h := checkLog_sound (w := (12527 / 237473)) (n := 12)
    (lo := (3300017 / 31250000)) (hi := (21120109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112473) = 1/(112473 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6795 : Bounds (-21120109 / 200000000) (-3300017 / 31250000) (Real.log (112473 / 125000)) := by
  have h := reflection_log_6795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6796_neg : (504701 / 50000000) ≤ -Real.log (15468074271 / 15625000000) ∧
    -Real.log (15468074271 / 15625000000) ≤ (10094021 / 1000000000) := by
  have h := checkLog_sound (w := (156925729 / 31093074271)) (n := 12)
    (lo := (504701 / 50000000)) (hi := (10094021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15468074271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15468074271) = 1/(15468074271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6796 : Bounds (-10094021 / 1000000000) (-504701 / 50000000) (Real.log (15468074271 / 15625000000)) := by
  have h := reflection_log_6796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6797_neg : (1004367 / 100000000) ≤ -Real.log (990006598911 / 1000000000000) ∧
    -Real.log (990006598911 / 1000000000000) ≤ (10043671 / 1000000000) := by
  have h := checkLog_sound (w := (9993401089 / 1990006598911)) (n := 12)
    (lo := (1004367 / 100000000)) (hi := (10043671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990006598911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990006598911) = 1/(990006598911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6797 : Bounds (-10043671 / 1000000000) (-1004367 / 100000000) (Real.log (990006598911 / 1000000000000)) := by
  have h := reflection_log_6797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6798_neg : (200604029 / 1000000000) ≤ -Real.log (62500000000 / 76383796483) ∧
    -Real.log (62500000000 / 76383796483) ≤ (20060403 / 100000000) := by
  have h := checkLog_sound (w := (13883796483 / 138883796483)) (n := 12)
    (lo := (200604029 / 1000000000)) (hi := (20060403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76383796483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76383796483 / 62500000000) = 1/(62500000000 / 76383796483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6798 : Bounds (200604029 / 1000000000) (20060403 / 100000000) (Real.log (76383796483 / 62500000000)) := by
  have h := reflection_log_6798_neg
  have he : Real.log (76383796483 / 62500000000) = -Real.log (62500000000 / 76383796483) := by
    rw [show ((76383796483 / 62500000000) : ℝ) = ((62500000000 / 76383796483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6799_neg : (50276767 / 250000000) ≤ -Real.log (250000000000 / 305688920897) ∧
    -Real.log (250000000000 / 305688920897) ≤ (201107069 / 1000000000) := by
  have h := checkLog_sound (w := (55688920897 / 555688920897)) (n := 12)
    (lo := (50276767 / 250000000)) (hi := (201107069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305688920897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305688920897 / 250000000000) = 1/(250000000000 / 305688920897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6799 : Bounds (50276767 / 250000000) (201107069 / 1000000000) (Real.log (305688920897 / 250000000000)) := by
  have h := reflection_log_6799_neg
  have he : Real.log (305688920897 / 250000000000) = -Real.log (250000000000 / 305688920897) := by
    rw [show ((305688920897 / 250000000000) : ℝ) = ((250000000000 / 305688920897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6800_neg : (201378753 / 500000000) ≤ -Real.log (250000000000 / 373986022713) ∧
    -Real.log (250000000000 / 373986022713) ≤ (402757507 / 1000000000) := by
  have h := checkLog_sound (w := (123986022713 / 623986022713)) (n := 12)
    (lo := (201378753 / 500000000)) (hi := (402757507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373986022713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373986022713 / 250000000000) = 1/(250000000000 / 373986022713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6800 : Bounds (201378753 / 500000000) (402757507 / 1000000000) (Real.log (373986022713 / 250000000000)) := by
  have h := reflection_log_6800_neg
  have he : Real.log (373986022713 / 250000000000) = -Real.log (250000000000 / 373986022713) := by
    rw [show ((373986022713 / 250000000000) : ℝ) = ((250000000000 / 373986022713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6801_neg : (402965731 / 1000000000) ≤ -Real.log (15625000000 / 23378994009) ∧
    -Real.log (15625000000 / 23378994009) ≤ (100741433 / 250000000) := by
  have h := checkLog_sound (w := (7753994009 / 39003994009)) (n := 12)
    (lo := (402965731 / 1000000000)) (hi := (100741433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23378994009 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23378994009 / 15625000000) = 1/(15625000000 / 23378994009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6801 : Bounds (402965731 / 1000000000) (100741433 / 250000000) (Real.log (23378994009 / 15625000000)) := by
  have h := reflection_log_6801_neg
  have he : Real.log (23378994009 / 15625000000) = -Real.log (15625000000 / 23378994009) := by
    rw [show ((23378994009 / 15625000000) : ℝ) = ((15625000000 / 23378994009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6802_neg : (181404469 / 1000000000) ≤ -Real.log (10000 / 11989) ∧
    -Real.log (10000 / 11989) ≤ (18140447 / 100000000) := by
  have h := checkLog_sound (w := (1989 / 21989)) (n := 12)
    (lo := (181404469 / 1000000000)) (hi := (18140447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11989 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11989 / 10000) = 1/(10000 / 11989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6802 : Bounds (181404469 / 1000000000) (18140447 / 100000000) (Real.log (11989 / 10000)) := by
  have h := reflection_log_6802_neg
  have he : Real.log (11989 / 10000) = -Real.log (10000 / 11989) := by
    rw [show ((11989 / 10000) : ℝ) = ((10000 / 11989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6803_neg : (44353899 / 200000000) ≤ -Real.log (8011 / 10000) ∧
    -Real.log (8011 / 10000) ≤ (27721187 / 125000000) := by
  have h := checkLog_sound (w := (1989 / 18011)) (n := 12)
    (lo := (44353899 / 200000000)) (hi := (27721187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8011) = 1/(8011 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6803 : Bounds (-27721187 / 125000000) (-44353899 / 200000000) (Real.log (8011 / 10000)) := by
  have h := reflection_log_6803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6804_neg : (1243 / 6250000) ≤ -Real.log (10000000 / 10001989) ∧
    -Real.log (10000000 / 10001989) ≤ (198881 / 1000000000) := by
  have h := checkLog_sound (w := (1989 / 20001989)) (n := 12)
    (lo := (1243 / 6250000)) (hi := (198881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001989 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001989 / 10000000) = 1/(10000000 / 10001989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6804 : Bounds (1243 / 6250000) (198881 / 1000000000) (Real.log (10001989 / 10000000)) := by
  have h := reflection_log_6804_neg
  have he : Real.log (10001989 / 10000000) = -Real.log (10000000 / 10001989) := by
    rw [show ((10001989 / 10000000) : ℝ) = ((10000000 / 10001989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6805_neg : (198919 / 1000000000) ≤ -Real.log (9998011 / 10000000) ∧
    -Real.log (9998011 / 10000000) ≤ (4973 / 25000000) := by
  have h := checkLog_sound (w := (1989 / 19998011)) (n := 12)
    (lo := (198919 / 1000000000)) (hi := (4973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998011) = 1/(9998011 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6805 : Bounds (-4973 / 25000000) (-198919 / 1000000000) (Real.log (9998011 / 10000000)) := by
  have h := reflection_log_6805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6806_neg : (95326543 / 1000000000) ≤ -Real.log (500000 / 550009) ∧
    -Real.log (500000 / 550009) ≤ (5957909 / 62500000) := by
  have h := checkLog_sound (w := (50009 / 1050009)) (n := 12)
    (lo := (95326543 / 1000000000)) (hi := (5957909 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550009 / 500000) = 1/(500000 / 550009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6806 : Bounds (95326543 / 1000000000) (5957909 / 62500000) (Real.log (550009 / 500000)) := by
  have h := reflection_log_6806_neg
  have he : Real.log (550009 / 500000) = -Real.log (500000 / 550009) := by
    rw [show ((550009 / 500000) : ℝ) = ((500000 / 550009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6807_neg : (21076103 / 200000000) ≤ -Real.log (449991 / 500000) ∧
    -Real.log (449991 / 500000) ≤ (26345129 / 250000000) := by
  have h := checkLog_sound (w := (50009 / 949991)) (n := 12)
    (lo := (21076103 / 200000000)) (hi := (26345129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449991) = 1/(449991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6807 : Bounds (-26345129 / 250000000) (-21076103 / 200000000) (Real.log (449991 / 500000)) := by
  have h := reflection_log_6807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6808_neg : (95552877 / 1000000000) ≤ -Real.log (1000000 / 1100267) ∧
    -Real.log (1000000 / 1100267) ≤ (47776439 / 500000000) := by
  have h := checkLog_sound (w := (100267 / 2100267)) (n := 12)
    (lo := (95552877 / 1000000000)) (hi := (47776439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100267 / 1000000) = 1/(1000000 / 1100267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6808 : Bounds (95552877 / 1000000000) (47776439 / 500000000) (Real.log (1100267 / 1000000)) := by
  have h := reflection_log_6808_neg
  have he : Real.log (1100267 / 1000000) = -Real.log (1000000 / 1100267) := by
    rw [show ((1100267 / 1000000) : ℝ) = ((1000000 / 1100267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6809_neg : (52828613 / 500000000) ≤ -Real.log (899733 / 1000000) ∧
    -Real.log (899733 / 1000000) ≤ (105657227 / 1000000000) := by
  have h := checkLog_sound (w := (100267 / 1899733)) (n := 12)
    (lo := (52828613 / 500000000)) (hi := (105657227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899733) = 1/(899733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6809 : Bounds (-105657227 / 1000000000) (-52828613 / 500000000) (Real.log (899733 / 1000000)) := by
  have h := reflection_log_6809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6810_neg : (2526087 / 250000000) ≤ -Real.log (989946528711 / 1000000000000) ∧
    -Real.log (989946528711 / 1000000000000) ≤ (10104349 / 1000000000) := by
  have h := checkLog_sound (w := (10053471289 / 1989946528711)) (n := 12)
    (lo := (2526087 / 250000000)) (hi := (10104349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989946528711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989946528711) = 1/(989946528711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6810 : Bounds (-10104349 / 1000000000) (-2526087 / 250000000) (Real.log (989946528711 / 1000000000000)) := by
  have h := reflection_log_6810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6811_neg : (2513493 / 250000000) ≤ -Real.log (247499099919 / 250000000000) ∧
    -Real.log (247499099919 / 250000000000) ≤ (10053973 / 1000000000) := by
  have h := checkLog_sound (w := (2500900081 / 497499099919)) (n := 12)
    (lo := (2513493 / 250000000)) (hi := (10053973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247499099919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247499099919) = 1/(247499099919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6811 : Bounds (-10053973 / 1000000000) (-2513493 / 250000000) (Real.log (247499099919 / 250000000000)) := by
  have h := reflection_log_6811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6812_neg : (200707059 / 1000000000) ≤ -Real.log (500000000000 / 611133333777) ∧
    -Real.log (500000000000 / 611133333777) ≤ (10035353 / 50000000) := by
  have h := checkLog_sound (w := (111133333777 / 1111133333777)) (n := 12)
    (lo := (200707059 / 1000000000)) (hi := (10035353 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611133333777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611133333777 / 500000000000) = 1/(500000000000 / 611133333777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6812 : Bounds (200707059 / 1000000000) (10035353 / 50000000) (Real.log (611133333777 / 500000000000)) := by
  have h := reflection_log_6812_neg
  have he : Real.log (611133333777 / 500000000000) = -Real.log (500000000000 / 611133333777) := by
    rw [show ((611133333777 / 500000000000) : ℝ) = ((500000000000 / 611133333777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6813_neg : (201210103 / 1000000000) ≤ -Real.log (3125000000 / 3821505241) ∧
    -Real.log (3125000000 / 3821505241) ≤ (25151263 / 125000000) := by
  have h := checkLog_sound (w := (696505241 / 6946505241)) (n := 12)
    (lo := (201210103 / 1000000000)) (hi := (25151263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821505241 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3821505241 / 3125000000) = 1/(3125000000 / 3821505241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6813 : Bounds (201210103 / 1000000000) (25151263 / 125000000) (Real.log (3821505241 / 3125000000)) := by
  have h := reflection_log_6813_neg
  have he : Real.log (3821505241 / 3125000000) = -Real.log (3125000000 / 3821505241) := by
    rw [show ((3821505241 / 3125000000) : ℝ) = ((3125000000 / 3821505241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6814_neg : (402965731 / 1000000000) ≤ -Real.log (500000000000 / 748127808287) ∧
    -Real.log (500000000000 / 748127808287) ≤ (100741433 / 250000000) := by
  have h := checkLog_sound (w := (248127808287 / 1248127808287)) (n := 12)
    (lo := (402965731 / 1000000000)) (hi := (100741433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748127808287 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748127808287 / 500000000000) = 1/(500000000000 / 748127808287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6814 : Bounds (402965731 / 1000000000) (100741433 / 250000000) (Real.log (748127808287 / 500000000000)) := by
  have h := reflection_log_6814_neg
  have he : Real.log (748127808287 / 500000000000) = -Real.log (500000000000 / 748127808287) := by
    rw [show ((748127808287 / 500000000000) : ℝ) = ((500000000000 / 748127808287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6815_neg : (80634793 / 200000000) ≤ -Real.log (500000000000 / 748283610037) ∧
    -Real.log (500000000000 / 748283610037) ≤ (201586983 / 500000000) := by
  have h := checkLog_sound (w := (248283610037 / 1248283610037)) (n := 12)
    (lo := (80634793 / 200000000)) (hi := (201586983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748283610037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748283610037 / 500000000000) = 1/(500000000000 / 748283610037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6815 : Bounds (80634793 / 200000000) (201586983 / 500000000) (Real.log (748283610037 / 500000000000)) := by
  have h := reflection_log_6815_neg
  have he : Real.log (748283610037 / 500000000000) = -Real.log (500000000000 / 748283610037) := by
    rw [show ((748283610037 / 500000000000) : ℝ) = ((500000000000 / 748283610037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6816_neg : (45371969 / 250000000) ≤ -Real.log (1000 / 1199) ∧
    -Real.log (1000 / 1199) ≤ (181487877 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2199)) (n := 12)
    (lo := (45371969 / 250000000)) (hi := (181487877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 1000) = 1/(1000 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6816 : Bounds (45371969 / 250000000) (181487877 / 1000000000) (Real.log (1199 / 1000)) := by
  have h := reflection_log_6816_neg
  have he : Real.log (1199 / 1000) = -Real.log (1000 / 1199) := by
    rw [show ((1199 / 1000) : ℝ) = ((1000 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6817_neg : (221894331 / 1000000000) ≤ -Real.log (801 / 1000) ∧
    -Real.log (801 / 1000) ≤ (55473583 / 250000000) := by
  have h := checkLog_sound (w := (199 / 1801)) (n := 12)
    (lo := (221894331 / 1000000000)) (hi := (55473583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 801) = 1/(801 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6817 : Bounds (-55473583 / 250000000) (-221894331 / 1000000000) (Real.log (801 / 1000)) := by
  have h := reflection_log_6817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6818_neg : (9949 / 50000000) ≤ -Real.log (1000000 / 1000199) ∧
    -Real.log (1000000 / 1000199) ≤ (198981 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2000199)) (n := 12)
    (lo := (9949 / 50000000)) (hi := (198981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000199 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000199 / 1000000) = 1/(1000000 / 1000199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6818 : Bounds (9949 / 50000000) (198981 / 1000000000) (Real.log (1000199 / 1000000)) := by
  have h := reflection_log_6818_neg
  have he : Real.log (1000199 / 1000000) = -Real.log (1000000 / 1000199) := by
    rw [show ((1000199 / 1000000) : ℝ) = ((1000000 / 1000199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6819_neg : (199019 / 1000000000) ≤ -Real.log (999801 / 1000000) ∧
    -Real.log (999801 / 1000000) ≤ (9951 / 50000000) := by
  have h := checkLog_sound (w := (199 / 1999801)) (n := 12)
    (lo := (199019 / 1000000000)) (hi := (9951 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999801) = 1/(999801 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6819 : Bounds (-9951 / 50000000) (-199019 / 1000000000) (Real.log (999801 / 1000000)) := by
  have h := reflection_log_6819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6820_neg : (19074581 / 200000000) ≤ -Real.log (1000000 / 1100069) ∧
    -Real.log (1000000 / 1100069) ≤ (47686453 / 500000000) := by
  have h := checkLog_sound (w := (100069 / 2100069)) (n := 12)
    (lo := (19074581 / 200000000)) (hi := (47686453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100069 / 1000000) = 1/(1000000 / 1100069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6820 : Bounds (19074581 / 200000000) (47686453 / 500000000) (Real.log (1100069 / 1000000)) := by
  have h := reflection_log_6820_neg
  have he : Real.log (1100069 / 1000000) = -Real.log (1000000 / 1100069) := by
    rw [show ((1100069 / 1000000) : ℝ) = ((1000000 / 1100069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6821_neg : (21087437 / 200000000) ≤ -Real.log (899931 / 1000000) ∧
    -Real.log (899931 / 1000000) ≤ (52718593 / 500000000) := by
  have h := checkLog_sound (w := (100069 / 1899931)) (n := 12)
    (lo := (21087437 / 200000000)) (hi := (52718593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899931) = 1/(899931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6821 : Bounds (-52718593 / 500000000) (-21087437 / 200000000) (Real.log (899931 / 1000000)) := by
  have h := reflection_log_6821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6822_neg : (23899807 / 250000000) ≤ -Real.log (500000 / 550159) ∧
    -Real.log (500000 / 550159) ≤ (95599229 / 1000000000) := by
  have h := checkLog_sound (w := (50159 / 1050159)) (n := 12)
    (lo := (23899807 / 250000000)) (hi := (95599229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550159 / 500000) = 1/(500000 / 550159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6822 : Bounds (23899807 / 250000000) (95599229 / 1000000000) (Real.log (550159 / 500000)) := by
  have h := reflection_log_6822_neg
  have he : Real.log (550159 / 500000) = -Real.log (500000 / 550159) := by
    rw [show ((550159 / 500000) : ℝ) = ((500000 / 550159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6823_neg : (105713911 / 1000000000) ≤ -Real.log (449841 / 500000) ∧
    -Real.log (449841 / 500000) ≤ (13214239 / 125000000) := by
  have h := checkLog_sound (w := (50159 / 949841)) (n := 12)
    (lo := (105713911 / 1000000000)) (hi := (13214239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449841) = 1/(449841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6823 : Bounds (-13214239 / 125000000) (-105713911 / 1000000000) (Real.log (449841 / 500000)) := by
  have h := reflection_log_6823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6824_neg : (5057341 / 500000000) ≤ -Real.log (247484074719 / 250000000000) ∧
    -Real.log (247484074719 / 250000000000) ≤ (10114683 / 1000000000) := by
  have h := checkLog_sound (w := (2515925281 / 497484074719)) (n := 12)
    (lo := (5057341 / 500000000)) (hi := (10114683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247484074719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247484074719) = 1/(247484074719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6824 : Bounds (-10114683 / 1000000000) (-5057341 / 500000000) (Real.log (247484074719 / 250000000000)) := by
  have h := reflection_log_6824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6825_neg : (251607 / 25000000) ≤ -Real.log (989986195239 / 1000000000000) ∧
    -Real.log (989986195239 / 1000000000000) ≤ (10064281 / 1000000000) := by
  have h := checkLog_sound (w := (10013804761 / 1989986195239)) (n := 12)
    (lo := (251607 / 25000000)) (hi := (10064281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989986195239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989986195239) = 1/(989986195239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6825 : Bounds (-10064281 / 1000000000) (-251607 / 25000000) (Real.log (989986195239 / 1000000000000)) := by
  have h := reflection_log_6825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6826_neg : (20081009 / 100000000) ≤ -Real.log (500000000000 / 611196302827) ∧
    -Real.log (500000000000 / 611196302827) ≤ (200810091 / 1000000000) := by
  have h := checkLog_sound (w := (111196302827 / 1111196302827)) (n := 12)
    (lo := (20081009 / 100000000)) (hi := (200810091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611196302827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611196302827 / 500000000000) = 1/(500000000000 / 611196302827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6826 : Bounds (20081009 / 100000000) (200810091 / 1000000000) (Real.log (611196302827 / 500000000000)) := by
  have h := reflection_log_6826_neg
  have he : Real.log (611196302827 / 500000000000) = -Real.log (500000000000 / 611196302827) := by
    rw [show ((611196302827 / 500000000000) : ℝ) = ((500000000000 / 611196302827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6827_neg : (10065657 / 50000000) ≤ -Real.log (500000000000 / 611503842469) ∧
    -Real.log (500000000000 / 611503842469) ≤ (201313141 / 1000000000) := by
  have h := checkLog_sound (w := (111503842469 / 1111503842469)) (n := 12)
    (lo := (10065657 / 50000000)) (hi := (201313141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611503842469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611503842469 / 500000000000) = 1/(500000000000 / 611503842469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6827 : Bounds (10065657 / 50000000) (201313141 / 1000000000) (Real.log (611503842469 / 500000000000)) := by
  have h := reflection_log_6827_neg
  have he : Real.log (611503842469 / 500000000000) = -Real.log (500000000000 / 611503842469) := by
    rw [show ((611503842469 / 500000000000) : ℝ) = ((500000000000 / 611503842469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6828_neg : (80634793 / 200000000) ≤ -Real.log (125000000000 / 187070902509) ∧
    -Real.log (125000000000 / 187070902509) ≤ (201586983 / 500000000) := by
  have h := checkLog_sound (w := (62070902509 / 312070902509)) (n := 12)
    (lo := (80634793 / 200000000)) (hi := (201586983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187070902509 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187070902509 / 125000000000) = 1/(125000000000 / 187070902509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6828 : Bounds (80634793 / 200000000) (201586983 / 500000000) (Real.log (187070902509 / 125000000000)) := by
  have h := reflection_log_6828_neg
  have he : Real.log (187070902509 / 125000000000) = -Real.log (125000000000 / 187070902509) := by
    rw [show ((187070902509 / 125000000000) : ℝ) = ((125000000000 / 187070902509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6829_neg : (403382207 / 1000000000) ≤ -Real.log (500000000000 / 748439450687) ∧
    -Real.log (500000000000 / 748439450687) ≤ (6302847 / 15625000) := by
  have h := checkLog_sound (w := (248439450687 / 1248439450687)) (n := 12)
    (lo := (403382207 / 1000000000)) (hi := (6302847 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748439450687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748439450687 / 500000000000) = 1/(500000000000 / 748439450687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6829 : Bounds (403382207 / 1000000000) (6302847 / 15625000) (Real.log (748439450687 / 500000000000)) := by
  have h := reflection_log_6829_neg
  have he : Real.log (748439450687 / 500000000000) = -Real.log (500000000000 / 748439450687) := by
    rw [show ((748439450687 / 500000000000) : ℝ) = ((500000000000 / 748439450687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6830_neg : (7262851 / 40000000) ≤ -Real.log (10000 / 11991) ∧
    -Real.log (10000 / 11991) ≤ (45392819 / 250000000) := by
  have h := checkLog_sound (w := (1991 / 21991)) (n := 12)
    (lo := (7262851 / 40000000)) (hi := (45392819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11991 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11991 / 10000) = 1/(10000 / 11991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6830 : Bounds (7262851 / 40000000) (45392819 / 250000000) (Real.log (11991 / 10000)) := by
  have h := reflection_log_6830_neg
  have he : Real.log (11991 / 10000) = -Real.log (10000 / 11991) := by
    rw [show ((11991 / 10000) : ℝ) = ((10000 / 11991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6831_neg : (222019183 / 1000000000) ≤ -Real.log (8009 / 10000) ∧
    -Real.log (8009 / 10000) ≤ (13876199 / 62500000) := by
  have h := checkLog_sound (w := (1991 / 18009)) (n := 12)
    (lo := (222019183 / 1000000000)) (hi := (13876199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8009) = 1/(8009 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6831 : Bounds (-13876199 / 62500000) (-222019183 / 1000000000) (Real.log (8009 / 10000)) := by
  have h := reflection_log_6831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6832_neg : (4977 / 25000000) ≤ -Real.log (10000000 / 10001991) ∧
    -Real.log (10000000 / 10001991) ≤ (199081 / 1000000000) := by
  have h := checkLog_sound (w := (1991 / 20001991)) (n := 12)
    (lo := (4977 / 25000000)) (hi := (199081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001991 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001991 / 10000000) = 1/(10000000 / 10001991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6832 : Bounds (4977 / 25000000) (199081 / 1000000000) (Real.log (10001991 / 10000000)) := by
  have h := reflection_log_6832_neg
  have he : Real.log (10001991 / 10000000) = -Real.log (10000000 / 10001991) := by
    rw [show ((10001991 / 10000000) : ℝ) = ((10000000 / 10001991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6833_neg : (199119 / 1000000000) ≤ -Real.log (9998009 / 10000000) ∧
    -Real.log (9998009 / 10000000) ≤ (2489 / 12500000) := by
  have h := checkLog_sound (w := (1991 / 19998009)) (n := 12)
    (lo := (199119 / 1000000000)) (hi := (2489 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998009) = 1/(9998009 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6833 : Bounds (-2489 / 12500000) (-199119 / 1000000000) (Real.log (9998009 / 10000000)) := by
  have h := reflection_log_6833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6834_neg : (745463 / 7812500) ≤ -Real.log (25000 / 27503) ∧
    -Real.log (25000 / 27503) ≤ (19083853 / 200000000) := by
  have h := checkLog_sound (w := (2503 / 52503)) (n := 12)
    (lo := (745463 / 7812500)) (hi := (19083853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27503 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27503 / 25000) = 1/(25000 / 27503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6834 : Bounds (745463 / 7812500) (19083853 / 200000000) (Real.log (27503 / 25000)) := by
  have h := reflection_log_6834_neg
  have he : Real.log (27503 / 25000) = -Real.log (25000 / 27503) := by
    rw [show ((27503 / 25000) : ℝ) = ((25000 / 27503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6835_neg : (105493857 / 1000000000) ≤ -Real.log (22497 / 25000) ∧
    -Real.log (22497 / 25000) ≤ (52746929 / 500000000) := by
  have h := checkLog_sound (w := (2503 / 47497)) (n := 12)
    (lo := (105493857 / 1000000000)) (hi := (52746929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22497) = 1/(22497 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6835 : Bounds (-52746929 / 500000000) (-105493857 / 1000000000) (Real.log (22497 / 25000)) := by
  have h := reflection_log_6835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6836_neg : (47822789 / 500000000) ≤ -Real.log (1000000 / 1100369) ∧
    -Real.log (1000000 / 1100369) ≤ (95645579 / 1000000000) := by
  have h := checkLog_sound (w := (100369 / 2100369)) (n := 12)
    (lo := (47822789 / 500000000)) (hi := (95645579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100369 / 1000000) = 1/(1000000 / 1100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6836 : Bounds (47822789 / 500000000) (95645579 / 1000000000) (Real.log (1100369 / 1000000)) := by
  have h := reflection_log_6836_neg
  have he : Real.log (1100369 / 1000000) = -Real.log (1000000 / 1100369) := by
    rw [show ((1100369 / 1000000) : ℝ) = ((1000000 / 1100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6837_neg : (105770599 / 1000000000) ≤ -Real.log (899631 / 1000000) ∧
    -Real.log (899631 / 1000000) ≤ (528853 / 5000000) := by
  have h := checkLog_sound (w := (100369 / 1899631)) (n := 12)
    (lo := (105770599 / 1000000000)) (hi := (528853 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899631) = 1/(899631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6837 : Bounds (-528853 / 5000000) (-105770599 / 1000000000) (Real.log (899631 / 1000000)) := by
  have h := reflection_log_6837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6838_neg : (10125021 / 1000000000) ≤ -Real.log (989926063839 / 1000000000000) ∧
    -Real.log (989926063839 / 1000000000000) ≤ (5062511 / 500000000) := by
  have h := checkLog_sound (w := (10073936161 / 1989926063839)) (n := 12)
    (lo := (10125021 / 1000000000)) (hi := (5062511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989926063839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989926063839) = 1/(989926063839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6838 : Bounds (-5062511 / 500000000) (-10125021 / 1000000000) (Real.log (989926063839 / 1000000000000)) := by
  have h := reflection_log_6838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6839_neg : (10074593 / 1000000000) ≤ -Real.log (618734991 / 625000000) ∧
    -Real.log (618734991 / 625000000) ≤ (5037297 / 500000000) := by
  have h := checkLog_sound (w := (6265009 / 1243734991)) (n := 12)
    (lo := (10074593 / 1000000000)) (hi := (5037297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618734991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618734991) = 1/(618734991 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6839 : Bounds (-5037297 / 500000000) (-10074593 / 1000000000) (Real.log (618734991 / 625000000)) := by
  have h := reflection_log_6839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6840_neg : (100456561 / 500000000) ≤ -Real.log (250000000000 / 305629639507) ∧
    -Real.log (250000000000 / 305629639507) ≤ (200913123 / 1000000000) := by
  have h := checkLog_sound (w := (55629639507 / 555629639507)) (n := 12)
    (lo := (100456561 / 500000000)) (hi := (200913123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305629639507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305629639507 / 250000000000) = 1/(250000000000 / 305629639507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6840 : Bounds (100456561 / 500000000) (200913123 / 1000000000) (Real.log (305629639507 / 250000000000)) := by
  have h := reflection_log_6840_neg
  have he : Real.log (305629639507 / 250000000000) = -Real.log (250000000000 / 305629639507) := by
    rw [show ((305629639507 / 250000000000) : ℝ) = ((250000000000 / 305629639507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6841_neg : (201416177 / 1000000000) ≤ -Real.log (250000000000 / 305783426761) ∧
    -Real.log (250000000000 / 305783426761) ≤ (100708089 / 500000000) := by
  have h := checkLog_sound (w := (55783426761 / 555783426761)) (n := 12)
    (lo := (201416177 / 1000000000)) (hi := (100708089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305783426761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305783426761 / 250000000000) = 1/(250000000000 / 305783426761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6841 : Bounds (201416177 / 1000000000) (100708089 / 500000000) (Real.log (305783426761 / 250000000000)) := by
  have h := reflection_log_6841_neg
  have he : Real.log (305783426761 / 250000000000) = -Real.log (250000000000 / 305783426761) := by
    rw [show ((305783426761 / 250000000000) : ℝ) = ((250000000000 / 305783426761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6842_neg : (403382207 / 1000000000) ≤ -Real.log (250000000000 / 374219725343) ∧
    -Real.log (250000000000 / 374219725343) ≤ (6302847 / 15625000) := by
  have h := checkLog_sound (w := (124219725343 / 624219725343)) (n := 12)
    (lo := (403382207 / 1000000000)) (hi := (6302847 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374219725343 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374219725343 / 250000000000) = 1/(250000000000 / 374219725343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6842 : Bounds (403382207 / 1000000000) (6302847 / 15625000) (Real.log (374219725343 / 250000000000)) := by
  have h := reflection_log_6842_neg
  have he : Real.log (374219725343 / 250000000000) = -Real.log (250000000000 / 374219725343) := by
    rw [show ((374219725343 / 250000000000) : ℝ) = ((250000000000 / 374219725343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6843_neg : (403590459 / 1000000000) ≤ -Real.log (250000000000 / 374297665127) ∧
    -Real.log (250000000000 / 374297665127) ≤ (20179523 / 50000000) := by
  have h := checkLog_sound (w := (124297665127 / 624297665127)) (n := 12)
    (lo := (403590459 / 1000000000)) (hi := (20179523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374297665127 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374297665127 / 250000000000) = 1/(250000000000 / 374297665127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6843 : Bounds (403590459 / 1000000000) (20179523 / 50000000) (Real.log (374297665127 / 250000000000)) := by
  have h := reflection_log_6843_neg
  have he : Real.log (374297665127 / 250000000000) = -Real.log (250000000000 / 374297665127) := by
    rw [show ((374297665127 / 250000000000) : ℝ) = ((250000000000 / 374297665127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6844_neg : (181654667 / 1000000000) ≤ -Real.log (1250 / 1499) ∧
    -Real.log (1250 / 1499) ≤ (45413667 / 250000000) := by
  have h := checkLog_sound (w := (249 / 2749)) (n := 12)
    (lo := (181654667 / 1000000000)) (hi := (45413667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1250) = 1/(1250 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6844 : Bounds (181654667 / 1000000000) (45413667 / 250000000) (Real.log (1499 / 1250)) := by
  have h := reflection_log_6844_neg
  have he : Real.log (1499 / 1250) = -Real.log (1250 / 1499) := by
    rw [show ((1499 / 1250) : ℝ) = ((1250 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6845_neg : (4442881 / 20000000) ≤ -Real.log (1001 / 1250) ∧
    -Real.log (1001 / 1250) ≤ (222144051 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 2251)) (n := 12)
    (lo := (4442881 / 20000000)) (hi := (222144051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1001) = 1/(1001 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6845 : Bounds (-222144051 / 1000000000) (-4442881 / 20000000) (Real.log (1001 / 1250)) := by
  have h := reflection_log_6845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6846_neg : (9959 / 50000000) ≤ -Real.log (1250000 / 1250249) ∧
    -Real.log (1250000 / 1250249) ≤ (199181 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 2500249)) (n := 12)
    (lo := (9959 / 50000000)) (hi := (199181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250249 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250249 / 1250000) = 1/(1250000 / 1250249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6846 : Bounds (9959 / 50000000) (199181 / 1000000000) (Real.log (1250249 / 1250000)) := by
  have h := reflection_log_6846_neg
  have he : Real.log (1250249 / 1250000) = -Real.log (1250000 / 1250249) := by
    rw [show ((1250249 / 1250000) : ℝ) = ((1250000 / 1250249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6847_neg : (199219 / 1000000000) ≤ -Real.log (1249751 / 1250000) ∧
    -Real.log (1249751 / 1250000) ≤ (9961 / 50000000) := by
  have h := checkLog_sound (w := (249 / 2499751)) (n := 12)
    (lo := (199219 / 1000000000)) (hi := (9961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249751) = 1/(1249751 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6847 : Bounds (-9961 / 50000000) (-199219 / 1000000000) (Real.log (1249751 / 1250000)) := by
  have h := reflection_log_6847_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0107 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6848_neg : (47732811 / 500000000) ≤ -Real.log (1000000 / 1100171) ∧
    -Real.log (1000000 / 1100171) ≤ (95465623 / 1000000000) := by
  have h := checkLog_sound (w := (100171 / 2100171)) (n := 12)
    (lo := (47732811 / 500000000)) (hi := (95465623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100171 / 1000000) = 1/(1000000 / 1100171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6848 : Bounds (47732811 / 500000000) (95465623 / 1000000000) (Real.log (1100171 / 1000000)) := by
  have h := reflection_log_6848_neg
  have he : Real.log (1100171 / 1000000) = -Real.log (1000000 / 1100171) := by
    rw [show ((1100171 / 1000000) : ℝ) = ((1000000 / 1100171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6849_neg : (105550533 / 1000000000) ≤ -Real.log (899829 / 1000000) ∧
    -Real.log (899829 / 1000000) ≤ (52775267 / 500000000) := by
  have h := checkLog_sound (w := (100171 / 1899829)) (n := 12)
    (lo := (105550533 / 1000000000)) (hi := (52775267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899829) = 1/(899829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6849 : Bounds (-52775267 / 500000000) (-105550533 / 1000000000) (Real.log (899829 / 1000000)) := by
  have h := reflection_log_6849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6850_neg : (3827677 / 40000000) ≤ -Real.log (50000 / 55021) ∧
    -Real.log (50000 / 55021) ≤ (47845963 / 500000000) := by
  have h := checkLog_sound (w := (5021 / 105021)) (n := 12)
    (lo := (3827677 / 40000000)) (hi := (47845963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55021 / 50000) = 1/(50000 / 55021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6850 : Bounds (3827677 / 40000000) (47845963 / 500000000) (Real.log (55021 / 50000)) := by
  have h := reflection_log_6850_neg
  have he : Real.log (55021 / 50000) = -Real.log (50000 / 55021) := by
    rw [show ((55021 / 50000) : ℝ) = ((50000 / 55021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6851_neg : (105827291 / 1000000000) ≤ -Real.log (44979 / 50000) ∧
    -Real.log (44979 / 50000) ≤ (26456823 / 250000000) := by
  have h := checkLog_sound (w := (5021 / 94979)) (n := 12)
    (lo := (105827291 / 1000000000)) (hi := (26456823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44979) = 1/(44979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6851 : Bounds (-26456823 / 250000000) (-105827291 / 1000000000) (Real.log (44979 / 50000)) := by
  have h := reflection_log_6851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6852_neg : (5067683 / 500000000) ≤ -Real.log (2474789559 / 2500000000) ∧
    -Real.log (2474789559 / 2500000000) ≤ (10135367 / 1000000000) := by
  have h := checkLog_sound (w := (25210441 / 4974789559)) (n := 12)
    (lo := (5067683 / 500000000)) (hi := (10135367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2474789559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2474789559) = 1/(2474789559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6852 : Bounds (-10135367 / 1000000000) (-5067683 / 500000000) (Real.log (2474789559 / 2500000000)) := by
  have h := reflection_log_6852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6853_neg : (10084911 / 1000000000) ≤ -Real.log (989965770759 / 1000000000000) ∧
    -Real.log (989965770759 / 1000000000000) ≤ (630307 / 62500000) := by
  have h := checkLog_sound (w := (10034229241 / 1989965770759)) (n := 12)
    (lo := (10084911 / 1000000000)) (hi := (630307 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989965770759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989965770759) = 1/(989965770759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6853 : Bounds (-630307 / 62500000) (-10084911 / 1000000000) (Real.log (989965770759 / 1000000000000)) := by
  have h := reflection_log_6853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6854_neg : (40203231 / 200000000) ≤ -Real.log (25000000000 / 30566113117) ∧
    -Real.log (25000000000 / 30566113117) ≤ (50254039 / 250000000) := by
  have h := checkLog_sound (w := (5566113117 / 55566113117)) (n := 12)
    (lo := (40203231 / 200000000)) (hi := (50254039 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30566113117 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30566113117 / 25000000000) = 1/(25000000000 / 30566113117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6854 : Bounds (40203231 / 200000000) (50254039 / 250000000) (Real.log (30566113117 / 25000000000)) := by
  have h := reflection_log_6854_neg
  have he : Real.log (30566113117 / 25000000000) = -Real.log (25000000000 / 30566113117) := by
    rw [show ((30566113117 / 25000000000) : ℝ) = ((25000000000 / 30566113117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6855_neg : (12594951 / 62500000) ≤ -Real.log (250000000000 / 305814935859) ∧
    -Real.log (250000000000 / 305814935859) ≤ (201519217 / 1000000000) := by
  have h := checkLog_sound (w := (55814935859 / 555814935859)) (n := 12)
    (lo := (12594951 / 62500000)) (hi := (201519217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305814935859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305814935859 / 250000000000) = 1/(250000000000 / 305814935859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6855 : Bounds (12594951 / 62500000) (201519217 / 1000000000) (Real.log (305814935859 / 250000000000)) := by
  have h := reflection_log_6855_neg
  have he : Real.log (305814935859 / 250000000000) = -Real.log (250000000000 / 305814935859) := by
    rw [show ((305814935859 / 250000000000) : ℝ) = ((250000000000 / 305814935859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6856_neg : (403590459 / 1000000000) ≤ -Real.log (500000000000 / 748595330253) ∧
    -Real.log (500000000000 / 748595330253) ≤ (20179523 / 50000000) := by
  have h := checkLog_sound (w := (248595330253 / 1248595330253)) (n := 12)
    (lo := (403590459 / 1000000000)) (hi := (20179523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748595330253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748595330253 / 500000000000) = 1/(500000000000 / 748595330253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6856 : Bounds (403590459 / 1000000000) (20179523 / 50000000) (Real.log (748595330253 / 500000000000)) := by
  have h := reflection_log_6856_neg
  have he : Real.log (748595330253 / 500000000000) = -Real.log (500000000000 / 748595330253) := by
    rw [show ((748595330253 / 500000000000) : ℝ) = ((500000000000 / 748595330253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6857_neg : (201899359 / 500000000) ≤ -Real.log (31250000000 / 46796953047) ∧
    -Real.log (31250000000 / 46796953047) ≤ (403798719 / 1000000000) := by
  have h := checkLog_sound (w := (15546953047 / 78046953047)) (n := 12)
    (lo := (201899359 / 500000000)) (hi := (403798719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46796953047 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46796953047 / 31250000000) = 1/(31250000000 / 46796953047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6857 : Bounds (201899359 / 500000000) (403798719 / 1000000000) (Real.log (46796953047 / 31250000000)) := by
  have h := reflection_log_6857_neg
  have he : Real.log (46796953047 / 31250000000) = -Real.log (31250000000 / 46796953047) := by
    rw [show ((46796953047 / 31250000000) : ℝ) = ((31250000000 / 46796953047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6858_neg : (181738053 / 1000000000) ≤ -Real.log (10000 / 11993) ∧
    -Real.log (10000 / 11993) ≤ (90869027 / 500000000) := by
  have h := checkLog_sound (w := (1993 / 21993)) (n := 12)
    (lo := (181738053 / 1000000000)) (hi := (90869027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 10000) = 1/(10000 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6858 : Bounds (181738053 / 1000000000) (90869027 / 500000000) (Real.log (11993 / 10000)) := by
  have h := reflection_log_6858_neg
  have he : Real.log (11993 / 10000) = -Real.log (10000 / 11993) := by
    rw [show ((11993 / 10000) : ℝ) = ((10000 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6859_neg : (222268933 / 1000000000) ≤ -Real.log (8007 / 10000) ∧
    -Real.log (8007 / 10000) ≤ (111134467 / 500000000) := by
  have h := checkLog_sound (w := (1993 / 18007)) (n := 12)
    (lo := (222268933 / 1000000000)) (hi := (111134467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8007) = 1/(8007 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6859 : Bounds (-111134467 / 500000000) (-222268933 / 1000000000) (Real.log (8007 / 10000)) := by
  have h := reflection_log_6859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6860_neg : (2491 / 12500000) ≤ -Real.log (10000000 / 10001993) ∧
    -Real.log (10000000 / 10001993) ≤ (199281 / 1000000000) := by
  have h := checkLog_sound (w := (1993 / 20001993)) (n := 12)
    (lo := (2491 / 12500000)) (hi := (199281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001993 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001993 / 10000000) = 1/(10000000 / 10001993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6860 : Bounds (2491 / 12500000) (199281 / 1000000000) (Real.log (10001993 / 10000000)) := by
  have h := reflection_log_6860_neg
  have he : Real.log (10001993 / 10000000) = -Real.log (10000000 / 10001993) := by
    rw [show ((10001993 / 10000000) : ℝ) = ((10000000 / 10001993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6861_neg : (199319 / 1000000000) ≤ -Real.log (9998007 / 10000000) ∧
    -Real.log (9998007 / 10000000) ≤ (4983 / 25000000) := by
  have h := checkLog_sound (w := (1993 / 19998007)) (n := 12)
    (lo := (199319 / 1000000000)) (hi := (4983 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998007) = 1/(9998007 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6861 : Bounds (-4983 / 25000000) (-199319 / 1000000000) (Real.log (9998007 / 10000000)) := by
  have h := reflection_log_6861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6862_neg : (95511977 / 1000000000) ≤ -Real.log (500000 / 550111) ∧
    -Real.log (500000 / 550111) ≤ (47755989 / 500000000) := by
  have h := checkLog_sound (w := (50111 / 1050111)) (n := 12)
    (lo := (95511977 / 1000000000)) (hi := (47755989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550111 / 500000) = 1/(500000 / 550111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6862 : Bounds (95511977 / 1000000000) (47755989 / 500000000) (Real.log (550111 / 500000)) := by
  have h := reflection_log_6862_neg
  have he : Real.log (550111 / 500000) = -Real.log (500000 / 550111) := by
    rw [show ((550111 / 500000) : ℝ) = ((500000 / 550111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6863_neg : (26401803 / 250000000) ≤ -Real.log (449889 / 500000) ∧
    -Real.log (449889 / 500000) ≤ (105607213 / 1000000000) := by
  have h := checkLog_sound (w := (50111 / 949889)) (n := 12)
    (lo := (26401803 / 250000000)) (hi := (105607213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449889) = 1/(449889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6863 : Bounds (-105607213 / 1000000000) (-26401803 / 250000000) (Real.log (449889 / 500000)) := by
  have h := reflection_log_6863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6864_neg : (47869589 / 500000000) ≤ -Real.log (125000 / 137559) ∧
    -Real.log (125000 / 137559) ≤ (95739179 / 1000000000) := by
  have h := checkLog_sound (w := (12559 / 262559)) (n := 12)
    (lo := (47869589 / 500000000)) (hi := (95739179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137559 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137559 / 125000) = 1/(125000 / 137559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6864 : Bounds (47869589 / 500000000) (95739179 / 1000000000) (Real.log (137559 / 125000)) := by
  have h := reflection_log_6864_neg
  have he : Real.log (137559 / 125000) = -Real.log (125000 / 137559) := by
    rw [show ((137559 / 125000) : ℝ) = ((125000 / 137559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6865_neg : (105885097 / 1000000000) ≤ -Real.log (112441 / 125000) ∧
    -Real.log (112441 / 125000) ≤ (52942549 / 500000000) := by
  have h := checkLog_sound (w := (12559 / 237441)) (n := 12)
    (lo := (105885097 / 1000000000)) (hi := (52942549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112441) = 1/(112441 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6865 : Bounds (-52942549 / 500000000) (-105885097 / 1000000000) (Real.log (112441 / 125000)) := by
  have h := reflection_log_6865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6866_neg : (5072959 / 500000000) ≤ -Real.log (15467271519 / 15625000000) ∧
    -Real.log (15467271519 / 15625000000) ≤ (10145919 / 1000000000) := by
  have h := checkLog_sound (w := (157728481 / 31092271519)) (n := 12)
    (lo := (5072959 / 500000000)) (hi := (10145919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15467271519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15467271519) = 1/(15467271519 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6866 : Bounds (-10145919 / 1000000000) (-5072959 / 500000000) (Real.log (15467271519 / 15625000000)) := by
  have h := reflection_log_6866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6867_neg : (2019047 / 200000000) ≤ -Real.log (247488887679 / 250000000000) ∧
    -Real.log (247488887679 / 250000000000) ≤ (2523809 / 250000000) := by
  have h := checkLog_sound (w := (2511112321 / 497488887679)) (n := 12)
    (lo := (2019047 / 200000000)) (hi := (2523809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247488887679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247488887679) = 1/(247488887679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6867 : Bounds (-2523809 / 250000000) (-2019047 / 200000000) (Real.log (247488887679 / 250000000000)) := by
  have h := reflection_log_6867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6868_neg : (20111919 / 100000000) ≤ -Real.log (250000000000 / 305692626403) ∧
    -Real.log (250000000000 / 305692626403) ≤ (201119191 / 1000000000) := by
  have h := checkLog_sound (w := (55692626403 / 555692626403)) (n := 12)
    (lo := (20111919 / 100000000)) (hi := (201119191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305692626403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305692626403 / 250000000000) = 1/(250000000000 / 305692626403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6868 : Bounds (20111919 / 100000000) (201119191 / 1000000000) (Real.log (305692626403 / 250000000000)) := by
  have h := reflection_log_6868_neg
  have he : Real.log (305692626403 / 250000000000) = -Real.log (250000000000 / 305692626403) := by
    rw [show ((305692626403 / 250000000000) : ℝ) = ((250000000000 / 305692626403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6869_neg : (50406069 / 250000000) ≤ -Real.log (125000000000 / 152923533231) ∧
    -Real.log (125000000000 / 152923533231) ≤ (201624277 / 1000000000) := by
  have h := checkLog_sound (w := (27923533231 / 277923533231)) (n := 12)
    (lo := (50406069 / 250000000)) (hi := (201624277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152923533231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152923533231 / 125000000000) = 1/(125000000000 / 152923533231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6869 : Bounds (50406069 / 250000000) (201624277 / 1000000000) (Real.log (152923533231 / 125000000000)) := by
  have h := reflection_log_6869_neg
  have he : Real.log (152923533231 / 125000000000) = -Real.log (125000000000 / 152923533231) := by
    rw [show ((152923533231 / 125000000000) : ℝ) = ((125000000000 / 152923533231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6870_neg : (201899359 / 500000000) ≤ -Real.log (500000000000 / 748751248751) ∧
    -Real.log (500000000000 / 748751248751) ≤ (403798719 / 1000000000) := by
  have h := checkLog_sound (w := (248751248751 / 1248751248751)) (n := 12)
    (lo := (201899359 / 500000000)) (hi := (403798719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748751248751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748751248751 / 500000000000) = 1/(500000000000 / 748751248751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6870 : Bounds (201899359 / 500000000) (403798719 / 1000000000) (Real.log (748751248751 / 500000000000)) := by
  have h := reflection_log_6870_neg
  have he : Real.log (748751248751 / 500000000000) = -Real.log (500000000000 / 748751248751) := by
    rw [show ((748751248751 / 500000000000) : ℝ) = ((500000000000 / 748751248751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6871_neg : (404006987 / 1000000000) ≤ -Real.log (100000000000 / 149781441239) ∧
    -Real.log (100000000000 / 149781441239) ≤ (101001747 / 250000000) := by
  have h := checkLog_sound (w := (49781441239 / 249781441239)) (n := 12)
    (lo := (404006987 / 1000000000)) (hi := (101001747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149781441239 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149781441239 / 100000000000) = 1/(100000000000 / 149781441239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6871 : Bounds (404006987 / 1000000000) (101001747 / 250000000) (Real.log (149781441239 / 100000000000)) := by
  have h := reflection_log_6871_neg
  have he : Real.log (149781441239 / 100000000000) = -Real.log (100000000000 / 149781441239) := by
    rw [show ((149781441239 / 100000000000) : ℝ) = ((100000000000 / 149781441239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6872_neg : (181821431 / 1000000000) ≤ -Real.log (5000 / 5997) ∧
    -Real.log (5000 / 5997) ≤ (22727679 / 125000000) := by
  have h := checkLog_sound (w := (997 / 10997)) (n := 12)
    (lo := (181821431 / 1000000000)) (hi := (22727679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5997 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5997 / 5000) = 1/(5000 / 5997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6872 : Bounds (181821431 / 1000000000) (22727679 / 125000000) (Real.log (5997 / 5000)) := by
  have h := reflection_log_6872_neg
  have he : Real.log (5997 / 5000) = -Real.log (5000 / 5997) := by
    rw [show ((5997 / 5000) : ℝ) = ((5000 / 5997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6873_neg : (27799229 / 125000000) ≤ -Real.log (4003 / 5000) ∧
    -Real.log (4003 / 5000) ≤ (222393833 / 1000000000) := by
  have h := checkLog_sound (w := (997 / 9003)) (n := 12)
    (lo := (27799229 / 125000000)) (hi := (222393833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4003) = 1/(4003 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6873 : Bounds (-222393833 / 1000000000) (-27799229 / 125000000) (Real.log (4003 / 5000)) := by
  have h := reflection_log_6873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6874_neg : (9969 / 50000000) ≤ -Real.log (5000000 / 5000997) ∧
    -Real.log (5000000 / 5000997) ≤ (199381 / 1000000000) := by
  have h := checkLog_sound (w := (997 / 10000997)) (n := 12)
    (lo := (9969 / 50000000)) (hi := (199381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000997 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000997 / 5000000) = 1/(5000000 / 5000997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6874 : Bounds (9969 / 50000000) (199381 / 1000000000) (Real.log (5000997 / 5000000)) := by
  have h := reflection_log_6874_neg
  have he : Real.log (5000997 / 5000000) = -Real.log (5000000 / 5000997) := by
    rw [show ((5000997 / 5000000) : ℝ) = ((5000000 / 5000997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6875_neg : (199419 / 1000000000) ≤ -Real.log (4999003 / 5000000) ∧
    -Real.log (4999003 / 5000000) ≤ (9971 / 50000000) := by
  have h := checkLog_sound (w := (997 / 9999003)) (n := 12)
    (lo := (199419 / 1000000000)) (hi := (9971 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999003) = 1/(4999003 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6875 : Bounds (-9971 / 50000000) (-199419 / 1000000000) (Real.log (4999003 / 5000000)) := by
  have h := reflection_log_6875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6876_neg : (9555833 / 100000000) ≤ -Real.log (1000000 / 1100273) ∧
    -Real.log (1000000 / 1100273) ≤ (95558331 / 1000000000) := by
  have h := checkLog_sound (w := (100273 / 2100273)) (n := 12)
    (lo := (9555833 / 100000000)) (hi := (95558331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100273 / 1000000) = 1/(1000000 / 1100273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6876 : Bounds (9555833 / 100000000) (95558331 / 1000000000) (Real.log (1100273 / 1000000)) := by
  have h := reflection_log_6876_neg
  have he : Real.log (1100273 / 1000000) = -Real.log (1000000 / 1100273) := by
    rw [show ((1100273 / 1000000) : ℝ) = ((1000000 / 1100273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6877_neg : (21132779 / 200000000) ≤ -Real.log (899727 / 1000000) ∧
    -Real.log (899727 / 1000000) ≤ (13207987 / 125000000) := by
  have h := checkLog_sound (w := (100273 / 1899727)) (n := 12)
    (lo := (21132779 / 200000000)) (hi := (13207987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899727) = 1/(899727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6877 : Bounds (-13207987 / 125000000) (-21132779 / 200000000) (Real.log (899727 / 1000000)) := by
  have h := reflection_log_6877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6878_neg : (95785521 / 1000000000) ≤ -Real.log (1000000 / 1100523) ∧
    -Real.log (1000000 / 1100523) ≤ (47892761 / 500000000) := by
  have h := checkLog_sound (w := (100523 / 2100523)) (n := 12)
    (lo := (95785521 / 1000000000)) (hi := (47892761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100523 / 1000000) = 1/(1000000 / 1100523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6878 : Bounds (95785521 / 1000000000) (47892761 / 500000000) (Real.log (1100523 / 1000000)) := by
  have h := reflection_log_6878_neg
  have he : Real.log (1100523 / 1000000) = -Real.log (1000000 / 1100523) := by
    rw [show ((1100523 / 1000000) : ℝ) = ((1000000 / 1100523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6879_neg : (21188359 / 200000000) ≤ -Real.log (899477 / 1000000) ∧
    -Real.log (899477 / 1000000) ≤ (26485449 / 250000000) := by
  have h := checkLog_sound (w := (100523 / 1899477)) (n := 12)
    (lo := (21188359 / 200000000)) (hi := (26485449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899477) = 1/(899477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6879 : Bounds (-26485449 / 250000000) (-21188359 / 200000000) (Real.log (899477 / 1000000)) := by
  have h := reflection_log_6879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6880_neg : (5078137 / 500000000) ≤ -Real.log (989895126471 / 1000000000000) ∧
    -Real.log (989895126471 / 1000000000000) ≤ (406251 / 40000000) := by
  have h := checkLog_sound (w := (10104873529 / 1989895126471)) (n := 12)
    (lo := (5078137 / 500000000)) (hi := (406251 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989895126471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989895126471) = 1/(989895126471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6880 : Bounds (-406251 / 40000000) (-5078137 / 500000000) (Real.log (989895126471 / 1000000000000)) := by
  have h := reflection_log_6880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6881_neg : (2526391 / 250000000) ≤ -Real.log (989945325471 / 1000000000000) ∧
    -Real.log (989945325471 / 1000000000000) ≤ (2021113 / 200000000) := by
  have h := checkLog_sound (w := (10054674529 / 1989945325471)) (n := 12)
    (lo := (2526391 / 250000000)) (hi := (2021113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989945325471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989945325471) = 1/(989945325471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6881 : Bounds (-2021113 / 200000000) (-2526391 / 250000000) (Real.log (989945325471 / 1000000000000)) := by
  have h := reflection_log_6881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6882_neg : (8048889 / 40000000) ≤ -Real.log (500000000000 / 611448250413) ∧
    -Real.log (500000000000 / 611448250413) ≤ (100611113 / 500000000) := by
  have h := checkLog_sound (w := (111448250413 / 1111448250413)) (n := 12)
    (lo := (8048889 / 40000000)) (hi := (100611113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611448250413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611448250413 / 500000000000) = 1/(500000000000 / 611448250413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6882 : Bounds (8048889 / 40000000) (100611113 / 500000000) (Real.log (611448250413 / 500000000000)) := by
  have h := reflection_log_6882_neg
  have he : Real.log (611448250413 / 500000000000) = -Real.log (500000000000 / 611448250413) := by
    rw [show ((611448250413 / 500000000000) : ℝ) = ((500000000000 / 611448250413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6883_neg : (201727317 / 1000000000) ≤ -Real.log (500000000000 / 611757165553) ∧
    -Real.log (500000000000 / 611757165553) ≤ (100863659 / 500000000) := by
  have h := checkLog_sound (w := (111757165553 / 1111757165553)) (n := 12)
    (lo := (201727317 / 1000000000)) (hi := (100863659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611757165553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611757165553 / 500000000000) = 1/(500000000000 / 611757165553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6883 : Bounds (201727317 / 1000000000) (100863659 / 500000000) (Real.log (611757165553 / 500000000000)) := by
  have h := reflection_log_6883_neg
  have he : Real.log (611757165553 / 500000000000) = -Real.log (500000000000 / 611757165553) := by
    rw [show ((611757165553 / 500000000000) : ℝ) = ((500000000000 / 611757165553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6884_neg : (404006987 / 1000000000) ≤ -Real.log (250000000000 / 374453603097) ∧
    -Real.log (250000000000 / 374453603097) ≤ (101001747 / 250000000) := by
  have h := checkLog_sound (w := (124453603097 / 624453603097)) (n := 12)
    (lo := (404006987 / 1000000000)) (hi := (101001747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374453603097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374453603097 / 250000000000) = 1/(250000000000 / 374453603097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6884 : Bounds (404006987 / 1000000000) (101001747 / 250000000) (Real.log (374453603097 / 250000000000)) := by
  have h := reflection_log_6884_neg
  have he : Real.log (374453603097 / 250000000000) = -Real.log (250000000000 / 374453603097) := by
    rw [show ((374453603097 / 250000000000) : ℝ) = ((250000000000 / 374453603097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6885_neg : (12631727 / 31250000) ≤ -Real.log (500000000000 / 749063202599) ∧
    -Real.log (500000000000 / 749063202599) ≤ (80843053 / 200000000) := by
  have h := checkLog_sound (w := (249063202599 / 1249063202599)) (n := 12)
    (lo := (12631727 / 31250000)) (hi := (80843053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749063202599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749063202599 / 500000000000) = 1/(500000000000 / 749063202599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6885 : Bounds (12631727 / 31250000) (80843053 / 200000000) (Real.log (749063202599 / 500000000000)) := by
  have h := reflection_log_6885_neg
  have he : Real.log (749063202599 / 500000000000) = -Real.log (500000000000 / 749063202599) := by
    rw [show ((749063202599 / 500000000000) : ℝ) = ((500000000000 / 749063202599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6886_neg : (181904803 / 1000000000) ≤ -Real.log (2000 / 2399) ∧
    -Real.log (2000 / 2399) ≤ (45476201 / 250000000) := by
  have h := checkLog_sound (w := (399 / 4399)) (n := 12)
    (lo := (181904803 / 1000000000)) (hi := (45476201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2399 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2399 / 2000) = 1/(2000 / 2399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6886 : Bounds (181904803 / 1000000000) (45476201 / 250000000) (Real.log (2399 / 2000)) := by
  have h := reflection_log_6886_neg
  have he : Real.log (2399 / 2000) = -Real.log (2000 / 2399) := by
    rw [show ((2399 / 2000) : ℝ) = ((2000 / 2399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6887_neg : (111259373 / 500000000) ≤ -Real.log (1601 / 2000) ∧
    -Real.log (1601 / 2000) ≤ (222518747 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 3601)) (n := 12)
    (lo := (111259373 / 500000000)) (hi := (222518747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1601) = 1/(1601 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6887 : Bounds (-222518747 / 1000000000) (-111259373 / 500000000) (Real.log (1601 / 2000)) := by
  have h := reflection_log_6887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6888_neg : (4987 / 25000000) ≤ -Real.log (2000000 / 2000399) ∧
    -Real.log (2000000 / 2000399) ≤ (199481 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 4000399)) (n := 12)
    (lo := (4987 / 25000000)) (hi := (199481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000399 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000399 / 2000000) = 1/(2000000 / 2000399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6888 : Bounds (4987 / 25000000) (199481 / 1000000000) (Real.log (2000399 / 2000000)) := by
  have h := reflection_log_6888_neg
  have he : Real.log (2000399 / 2000000) = -Real.log (2000000 / 2000399) := by
    rw [show ((2000399 / 2000000) : ℝ) = ((2000000 / 2000399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6889_neg : (199519 / 1000000000) ≤ -Real.log (1999601 / 2000000) ∧
    -Real.log (1999601 / 2000000) ≤ (1247 / 6250000) := by
  have h := checkLog_sound (w := (399 / 3999601)) (n := 12)
    (lo := (199519 / 1000000000)) (hi := (1247 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999601) = 1/(1999601 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6889 : Bounds (-1247 / 6250000) (-199519 / 1000000000) (Real.log (1999601 / 2000000)) := by
  have h := reflection_log_6889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6890_neg : (95604681 / 1000000000) ≤ -Real.log (250000 / 275081) ∧
    -Real.log (250000 / 275081) ≤ (47802341 / 500000000) := by
  have h := checkLog_sound (w := (25081 / 525081)) (n := 12)
    (lo := (95604681 / 1000000000)) (hi := (47802341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275081 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275081 / 250000) = 1/(250000 / 275081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6890 : Bounds (95604681 / 1000000000) (47802341 / 500000000) (Real.log (275081 / 250000)) := by
  have h := reflection_log_6890_neg
  have he : Real.log (275081 / 250000) = -Real.log (250000 / 275081) := by
    rw [show ((275081 / 250000) : ℝ) = ((250000 / 275081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6891_neg : (5286029 / 50000000) ≤ -Real.log (224919 / 250000) ∧
    -Real.log (224919 / 250000) ≤ (105720581 / 1000000000) := by
  have h := checkLog_sound (w := (25081 / 474919)) (n := 12)
    (lo := (5286029 / 50000000)) (hi := (105720581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 224919) = 1/(224919 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6891 : Bounds (-105720581 / 1000000000) (-5286029 / 50000000) (Real.log (224919 / 250000)) := by
  have h := reflection_log_6891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6892_neg : (95831861 / 1000000000) ≤ -Real.log (500000 / 550287) ∧
    -Real.log (500000 / 550287) ≤ (47915931 / 500000000) := by
  have h := checkLog_sound (w := (50287 / 1050287)) (n := 12)
    (lo := (95831861 / 1000000000)) (hi := (47915931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550287 / 500000) = 1/(500000 / 550287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6892 : Bounds (95831861 / 1000000000) (47915931 / 500000000) (Real.log (550287 / 500000)) := by
  have h := reflection_log_6892_neg
  have he : Real.log (550287 / 500000) = -Real.log (500000 / 550287) := by
    rw [show ((550287 / 500000) : ℝ) = ((500000 / 550287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6893_neg : (3312453 / 31250000) ≤ -Real.log (449713 / 500000) ∧
    -Real.log (449713 / 500000) ≤ (105998497 / 1000000000) := by
  have h := checkLog_sound (w := (50287 / 949713)) (n := 12)
    (lo := (3312453 / 31250000)) (hi := (105998497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449713) = 1/(449713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6893 : Bounds (-105998497 / 1000000000) (-3312453 / 31250000) (Real.log (449713 / 500000)) := by
  have h := reflection_log_6893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6894_neg : (2033327 / 200000000) ≤ -Real.log (247471217631 / 250000000000) ∧
    -Real.log (247471217631 / 250000000000) ≤ (2541659 / 250000000) := by
  have h := checkLog_sound (w := (2528782369 / 497471217631)) (n := 12)
    (lo := (2033327 / 200000000)) (hi := (2541659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247471217631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247471217631) = 1/(247471217631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6894 : Bounds (-2541659 / 250000000) (-2033327 / 200000000) (Real.log (247471217631 / 250000000000)) := by
  have h := reflection_log_6894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6895_neg : (5057949 / 500000000) ≤ -Real.log (61870943439 / 62500000000) ∧
    -Real.log (61870943439 / 62500000000) ≤ (10115899 / 1000000000) := by
  have h := checkLog_sound (w := (629056561 / 124370943439)) (n := 12)
    (lo := (5057949 / 500000000)) (hi := (10115899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61870943439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61870943439) = 1/(61870943439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6895 : Bounds (-10115899 / 1000000000) (-5057949 / 500000000) (Real.log (61870943439 / 62500000000)) := by
  have h := reflection_log_6895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6896_neg : (100662631 / 500000000) ≤ -Real.log (250000000000 / 305755627581) ∧
    -Real.log (250000000000 / 305755627581) ≤ (201325263 / 1000000000) := by
  have h := checkLog_sound (w := (55755627581 / 555755627581)) (n := 12)
    (lo := (100662631 / 500000000)) (hi := (201325263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305755627581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305755627581 / 250000000000) = 1/(250000000000 / 305755627581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6896 : Bounds (100662631 / 500000000) (201325263 / 1000000000) (Real.log (305755627581 / 250000000000)) := by
  have h := reflection_log_6896_neg
  have he : Real.log (305755627581 / 250000000000) = -Real.log (250000000000 / 305755627581) := by
    rw [show ((305755627581 / 250000000000) : ℝ) = ((250000000000 / 305755627581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6897_neg : (100915179 / 500000000) ≤ -Real.log (500000000000 / 611820205331) ∧
    -Real.log (500000000000 / 611820205331) ≤ (201830359 / 1000000000) := by
  have h := checkLog_sound (w := (111820205331 / 1111820205331)) (n := 12)
    (lo := (100915179 / 500000000)) (hi := (201830359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611820205331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611820205331 / 500000000000) = 1/(500000000000 / 611820205331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6897 : Bounds (100915179 / 500000000) (201830359 / 1000000000) (Real.log (611820205331 / 500000000000)) := by
  have h := reflection_log_6897_neg
  have he : Real.log (611820205331 / 500000000000) = -Real.log (500000000000 / 611820205331) := by
    rw [show ((611820205331 / 500000000000) : ℝ) = ((500000000000 / 611820205331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6898_neg : (12631727 / 31250000) ≤ -Real.log (250000000000 / 374531601299) ∧
    -Real.log (250000000000 / 374531601299) ≤ (80843053 / 200000000) := by
  have h := checkLog_sound (w := (124531601299 / 624531601299)) (n := 12)
    (lo := (12631727 / 31250000)) (hi := (80843053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374531601299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374531601299 / 250000000000) = 1/(250000000000 / 374531601299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6898 : Bounds (12631727 / 31250000) (80843053 / 200000000) (Real.log (374531601299 / 250000000000)) := by
  have h := reflection_log_6898_neg
  have he : Real.log (374531601299 / 250000000000) = -Real.log (250000000000 / 374531601299) := by
    rw [show ((374531601299 / 250000000000) : ℝ) = ((250000000000 / 374531601299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6899_neg : (404423549 / 1000000000) ≤ -Real.log (500000000000 / 749219237977) ∧
    -Real.log (500000000000 / 749219237977) ≤ (8088471 / 20000000) := by
  have h := checkLog_sound (w := (249219237977 / 1249219237977)) (n := 12)
    (lo := (404423549 / 1000000000)) (hi := (8088471 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749219237977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749219237977 / 500000000000) = 1/(500000000000 / 749219237977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6899 : Bounds (404423549 / 1000000000) (8088471 / 20000000) (Real.log (749219237977 / 500000000000)) := by
  have h := reflection_log_6899_neg
  have he : Real.log (749219237977 / 500000000000) = -Real.log (500000000000 / 749219237977) := by
    rw [show ((749219237977 / 500000000000) : ℝ) = ((500000000000 / 749219237977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6900_neg : (181988167 / 1000000000) ≤ -Real.log (2500 / 2999) ∧
    -Real.log (2500 / 2999) ≤ (22748521 / 125000000) := by
  have h := checkLog_sound (w := (499 / 5499)) (n := 12)
    (lo := (181988167 / 1000000000)) (hi := (22748521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2999 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2999 / 2500) = 1/(2500 / 2999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6900 : Bounds (181988167 / 1000000000) (22748521 / 125000000) (Real.log (2999 / 2500)) := by
  have h := reflection_log_6900_neg
  have he : Real.log (2999 / 2500) = -Real.log (2500 / 2999) := by
    rw [show ((2999 / 2500) : ℝ) = ((2500 / 2999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6901_neg : (55660919 / 250000000) ≤ -Real.log (2001 / 2500) ∧
    -Real.log (2001 / 2500) ≤ (222643677 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4501)) (n := 12)
    (lo := (55660919 / 250000000)) (hi := (222643677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2001) = 1/(2001 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6901 : Bounds (-222643677 / 1000000000) (-55660919 / 250000000) (Real.log (2001 / 2500)) := by
  have h := reflection_log_6901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6902_neg : (9979 / 50000000) ≤ -Real.log (2500000 / 2500499) ∧
    -Real.log (2500000 / 2500499) ≤ (199581 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 5000499)) (n := 12)
    (lo := (9979 / 50000000)) (hi := (199581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500499 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500499 / 2500000) = 1/(2500000 / 2500499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6902 : Bounds (9979 / 50000000) (199581 / 1000000000) (Real.log (2500499 / 2500000)) := by
  have h := reflection_log_6902_neg
  have he : Real.log (2500499 / 2500000) = -Real.log (2500000 / 2500499) := by
    rw [show ((2500499 / 2500000) : ℝ) = ((2500000 / 2500499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6903_neg : (199619 / 1000000000) ≤ -Real.log (2499501 / 2500000) ∧
    -Real.log (2499501 / 2500000) ≤ (9981 / 50000000) := by
  have h := checkLog_sound (w := (499 / 4999501)) (n := 12)
    (lo := (199619 / 1000000000)) (hi := (9981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499501) = 1/(2499501 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6903 : Bounds (-9981 / 50000000) (-199619 / 1000000000) (Real.log (2499501 / 2500000)) := by
  have h := reflection_log_6903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6904_neg : (9565103 / 100000000) ≤ -Real.log (8000 / 8803) ∧
    -Real.log (8000 / 8803) ≤ (95651031 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 16803)) (n := 12)
    (lo := (9565103 / 100000000)) (hi := (95651031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8803 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8803 / 8000) = 1/(8000 / 8803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6904 : Bounds (9565103 / 100000000) (95651031 / 1000000000) (Real.log (8803 / 8000)) := by
  have h := reflection_log_6904_neg
  have he : Real.log (8803 / 8000) = -Real.log (8000 / 8803) := by
    rw [show ((8803 / 8000) : ℝ) = ((8000 / 8803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6905_neg : (105777269 / 1000000000) ≤ -Real.log (7197 / 8000) ∧
    -Real.log (7197 / 8000) ≤ (10577727 / 100000000) := by
  have h := checkLog_sound (w := (803 / 15197)) (n := 12)
    (lo := (105777269 / 1000000000)) (hi := (10577727 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7197) = 1/(7197 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6905 : Bounds (-10577727 / 100000000) (-105777269 / 1000000000) (Real.log (7197 / 8000)) := by
  have h := reflection_log_6905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6906_neg : (479391 / 5000000) ≤ -Real.log (1600 / 1761) ∧
    -Real.log (1600 / 1761) ≤ (95878201 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 3361)) (n := 12)
    (lo := (479391 / 5000000)) (hi := (95878201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1600) = 1/(1600 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6906 : Bounds (479391 / 5000000) (95878201 / 1000000000) (Real.log (1761 / 1600)) := by
  have h := reflection_log_6906_neg
  have he : Real.log (1761 / 1600) = -Real.log (1600 / 1761) := by
    rw [show ((1761 / 1600) : ℝ) = ((1600 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6907_neg : (106055201 / 1000000000) ≤ -Real.log (1439 / 1600) ∧
    -Real.log (1439 / 1600) ≤ (53027601 / 500000000) := by
  have h := checkLog_sound (w := (161 / 3039)) (n := 12)
    (lo := (106055201 / 1000000000)) (hi := (53027601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 1439) = 1/(1439 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6907 : Bounds (-53027601 / 500000000) (-106055201 / 1000000000) (Real.log (1439 / 1600)) := by
  have h := reflection_log_6907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6908_neg : (10177001 / 1000000000) ≤ -Real.log (2534079 / 2560000) ∧
    -Real.log (2534079 / 2560000) ≤ (5088501 / 500000000) := by
  have h := checkLog_sound (w := (25921 / 5094079)) (n := 12)
    (lo := (10177001 / 1000000000)) (hi := (5088501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 2534079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 2534079) = 1/(2534079 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6908 : Bounds (-5088501 / 500000000) (-10177001 / 1000000000) (Real.log (2534079 / 2560000)) := by
  have h := reflection_log_6908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6909_neg : (5063119 / 500000000) ≤ -Real.log (63355191 / 64000000) ∧
    -Real.log (63355191 / 64000000) ≤ (10126239 / 1000000000) := by
  have h := checkLog_sound (w := (644809 / 127355191)) (n := 12)
    (lo := (5063119 / 500000000)) (hi := (10126239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 63355191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 63355191) = 1/(63355191 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6909 : Bounds (-10126239 / 1000000000) (-5063119 / 500000000) (Real.log (63355191 / 64000000)) := by
  have h := reflection_log_6909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6910_neg : (201428299 / 1000000000) ≤ -Real.log (100000000000 / 122314853411) ∧
    -Real.log (100000000000 / 122314853411) ≤ (2014283 / 10000000) := by
  have h := checkLog_sound (w := (22314853411 / 222314853411)) (n := 12)
    (lo := (201428299 / 1000000000)) (hi := (2014283 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122314853411 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122314853411 / 100000000000) = 1/(100000000000 / 122314853411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6910 : Bounds (201428299 / 1000000000) (2014283 / 10000000) (Real.log (122314853411 / 100000000000)) := by
  have h := reflection_log_6910_neg
  have he : Real.log (122314853411 / 100000000000) = -Real.log (100000000000 / 122314853411) := by
    rw [show ((122314853411 / 100000000000) : ℝ) = ((100000000000 / 122314853411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6911_neg : (201933401 / 1000000000) ≤ -Real.log (500000000000 / 611883252259) ∧
    -Real.log (500000000000 / 611883252259) ≤ (100966701 / 500000000) := by
  have h := checkLog_sound (w := (111883252259 / 1111883252259)) (n := 12)
    (lo := (201933401 / 1000000000)) (hi := (100966701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611883252259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611883252259 / 500000000000) = 1/(500000000000 / 611883252259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6911 : Bounds (201933401 / 1000000000) (100966701 / 500000000) (Real.log (611883252259 / 500000000000)) := by
  have h := reflection_log_6911_neg
  have he : Real.log (611883252259 / 500000000000) = -Real.log (500000000000 / 611883252259) := by
    rw [show ((611883252259 / 500000000000) : ℝ) = ((500000000000 / 611883252259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0108 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6912_neg : (404423549 / 1000000000) ≤ -Real.log (62500000000 / 93652404747) ∧
    -Real.log (62500000000 / 93652404747) ≤ (8088471 / 20000000) := by
  have h := checkLog_sound (w := (31152404747 / 156152404747)) (n := 12)
    (lo := (404423549 / 1000000000)) (hi := (8088471 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93652404747 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93652404747 / 62500000000) = 1/(62500000000 / 93652404747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6912 : Bounds (404423549 / 1000000000) (8088471 / 20000000) (Real.log (93652404747 / 62500000000)) := by
  have h := reflection_log_6912_neg
  have he : Real.log (93652404747 / 62500000000) = -Real.log (62500000000 / 93652404747) := by
    rw [show ((93652404747 / 62500000000) : ℝ) = ((62500000000 / 93652404747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6913_neg : (101157961 / 250000000) ≤ -Real.log (62500000000 / 93671914043) ∧
    -Real.log (62500000000 / 93671914043) ≤ (80926369 / 200000000) := by
  have h := checkLog_sound (w := (31171914043 / 156171914043)) (n := 12)
    (lo := (101157961 / 250000000)) (hi := (80926369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93671914043 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93671914043 / 62500000000) = 1/(62500000000 / 93671914043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6913 : Bounds (101157961 / 250000000) (80926369 / 200000000) (Real.log (93671914043 / 62500000000)) := by
  have h := reflection_log_6913_neg
  have he : Real.log (93671914043 / 62500000000) = -Real.log (62500000000 / 93671914043) := by
    rw [show ((93671914043 / 62500000000) : ℝ) = ((62500000000 / 93671914043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6914_neg : (7282861 / 40000000) ≤ -Real.log (10000 / 11997) ∧
    -Real.log (10000 / 11997) ≤ (91035763 / 500000000) := by
  have h := checkLog_sound (w := (1997 / 21997)) (n := 12)
    (lo := (7282861 / 40000000)) (hi := (91035763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11997 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11997 / 10000) = 1/(10000 / 11997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6914 : Bounds (7282861 / 40000000) (91035763 / 500000000) (Real.log (11997 / 10000)) := by
  have h := reflection_log_6914_neg
  have he : Real.log (11997 / 10000) = -Real.log (10000 / 11997) := by
    rw [show ((11997 / 10000) : ℝ) = ((10000 / 11997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6915_neg : (222768621 / 1000000000) ≤ -Real.log (8003 / 10000) ∧
    -Real.log (8003 / 10000) ≤ (111384311 / 500000000) := by
  have h := checkLog_sound (w := (1997 / 18003)) (n := 12)
    (lo := (222768621 / 1000000000)) (hi := (111384311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8003) = 1/(8003 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6915 : Bounds (-111384311 / 500000000) (-222768621 / 1000000000) (Real.log (8003 / 10000)) := by
  have h := reflection_log_6915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6916_neg : (78 / 390625) ≤ -Real.log (10000000 / 10001997) ∧
    -Real.log (10000000 / 10001997) ≤ (199681 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 20001997)) (n := 12)
    (lo := (78 / 390625)) (hi := (199681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001997 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001997 / 10000000) = 1/(10000000 / 10001997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6916 : Bounds (78 / 390625) (199681 / 1000000000) (Real.log (10001997 / 10000000)) := by
  have h := reflection_log_6916_neg
  have he : Real.log (10001997 / 10000000) = -Real.log (10000000 / 10001997) := by
    rw [show ((10001997 / 10000000) : ℝ) = ((10000000 / 10001997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6917_neg : (199719 / 1000000000) ≤ -Real.log (9998003 / 10000000) ∧
    -Real.log (9998003 / 10000000) ≤ (4993 / 25000000) := by
  have h := checkLog_sound (w := (1997 / 19998003)) (n := 12)
    (lo := (199719 / 1000000000)) (hi := (4993 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998003) = 1/(9998003 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6917 : Bounds (-4993 / 25000000) (-199719 / 1000000000) (Real.log (9998003 / 10000000)) := by
  have h := reflection_log_6917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6918_neg : (95697377 / 1000000000) ≤ -Real.log (500000 / 550213) ∧
    -Real.log (500000 / 550213) ≤ (47848689 / 500000000) := by
  have h := checkLog_sound (w := (50213 / 1050213)) (n := 12)
    (lo := (95697377 / 1000000000)) (hi := (47848689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550213 / 500000) = 1/(500000 / 550213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6918 : Bounds (95697377 / 1000000000) (47848689 / 500000000) (Real.log (550213 / 500000)) := by
  have h := reflection_log_6918_neg
  have he : Real.log (550213 / 500000) = -Real.log (500000 / 550213) := by
    rw [show ((550213 / 500000) : ℝ) = ((500000 / 550213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6919_neg : (105833961 / 1000000000) ≤ -Real.log (449787 / 500000) ∧
    -Real.log (449787 / 500000) ≤ (52916981 / 500000000) := by
  have h := checkLog_sound (w := (50213 / 949787)) (n := 12)
    (lo := (105833961 / 1000000000)) (hi := (52916981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449787) = 1/(449787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6919 : Bounds (-52916981 / 500000000) (-105833961 / 1000000000) (Real.log (449787 / 500000)) := by
  have h := reflection_log_6919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6920_neg : (11990567 / 125000000) ≤ -Real.log (250000 / 275169) ∧
    -Real.log (250000 / 275169) ≤ (95924537 / 1000000000) := by
  have h := checkLog_sound (w := (25169 / 525169)) (n := 12)
    (lo := (11990567 / 125000000)) (hi := (95924537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275169 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275169 / 250000) = 1/(250000 / 275169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6920 : Bounds (11990567 / 125000000) (95924537 / 1000000000) (Real.log (275169 / 250000)) := by
  have h := reflection_log_6920_neg
  have he : Real.log (275169 / 250000) = -Real.log (250000 / 275169) := by
    rw [show ((275169 / 250000) : ℝ) = ((250000 / 275169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6921_neg : (26527977 / 250000000) ≤ -Real.log (224831 / 250000) ∧
    -Real.log (224831 / 250000) ≤ (106111909 / 1000000000) := by
  have h := checkLog_sound (w := (25169 / 474831)) (n := 12)
    (lo := (26527977 / 250000000)) (hi := (106111909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 224831) = 1/(224831 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6921 : Bounds (-106111909 / 1000000000) (-26527977 / 250000000) (Real.log (224831 / 250000)) := by
  have h := reflection_log_6921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6922_neg : (2546843 / 250000000) ≤ -Real.log (61866521439 / 62500000000) ∧
    -Real.log (61866521439 / 62500000000) ≤ (10187373 / 1000000000) := by
  have h := checkLog_sound (w := (633478561 / 124366521439)) (n := 12)
    (lo := (2546843 / 250000000)) (hi := (10187373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61866521439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61866521439) = 1/(61866521439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6922 : Bounds (-10187373 / 1000000000) (-2546843 / 250000000) (Real.log (61866521439 / 62500000000)) := by
  have h := reflection_log_6922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6923_neg : (10136583 / 1000000000) ≤ -Real.log (247478654631 / 250000000000) ∧
    -Real.log (247478654631 / 250000000000) ≤ (1267073 / 125000000) := by
  have h := checkLog_sound (w := (2521345369 / 497478654631)) (n := 12)
    (lo := (10136583 / 1000000000)) (hi := (1267073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247478654631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247478654631) = 1/(247478654631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6923 : Bounds (-1267073 / 125000000) (-10136583 / 1000000000) (Real.log (247478654631 / 250000000000)) := by
  have h := reflection_log_6923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6924_neg : (100765669 / 500000000) ≤ -Real.log (500000000000 / 611637286093) ∧
    -Real.log (500000000000 / 611637286093) ≤ (201531339 / 1000000000) := by
  have h := checkLog_sound (w := (111637286093 / 1111637286093)) (n := 12)
    (lo := (100765669 / 500000000)) (hi := (201531339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611637286093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611637286093 / 500000000000) = 1/(500000000000 / 611637286093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6924 : Bounds (100765669 / 500000000) (201531339 / 1000000000) (Real.log (611637286093 / 500000000000)) := by
  have h := reflection_log_6924_neg
  have he : Real.log (611637286093 / 500000000000) = -Real.log (500000000000 / 611637286093) := by
    rw [show ((611637286093 / 500000000000) : ℝ) = ((500000000000 / 611637286093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6925_neg : (40407289 / 200000000) ≤ -Real.log (500000000000 / 611946306337) ∧
    -Real.log (500000000000 / 611946306337) ≤ (101018223 / 500000000) := by
  have h := checkLog_sound (w := (111946306337 / 1111946306337)) (n := 12)
    (lo := (40407289 / 200000000)) (hi := (101018223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611946306337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611946306337 / 500000000000) = 1/(500000000000 / 611946306337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6925 : Bounds (40407289 / 200000000) (101018223 / 500000000) (Real.log (611946306337 / 500000000000)) := by
  have h := reflection_log_6925_neg
  have he : Real.log (611946306337 / 500000000000) = -Real.log (500000000000 / 611946306337) := by
    rw [show ((611946306337 / 500000000000) : ℝ) = ((500000000000 / 611946306337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6926_neg : (101157961 / 250000000) ≤ -Real.log (500000000000 / 749375312343) ∧
    -Real.log (500000000000 / 749375312343) ≤ (80926369 / 200000000) := by
  have h := checkLog_sound (w := (249375312343 / 1249375312343)) (n := 12)
    (lo := (101157961 / 250000000)) (hi := (80926369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749375312343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749375312343 / 500000000000) = 1/(500000000000 / 749375312343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6926 : Bounds (101157961 / 250000000) (80926369 / 200000000) (Real.log (749375312343 / 500000000000)) := by
  have h := reflection_log_6926_neg
  have he : Real.log (749375312343 / 500000000000) = -Real.log (500000000000 / 749375312343) := by
    rw [show ((749375312343 / 500000000000) : ℝ) = ((500000000000 / 749375312343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6927_neg : (404840147 / 1000000000) ≤ -Real.log (125000000000 / 187382856429) ∧
    -Real.log (125000000000 / 187382856429) ≤ (101210037 / 250000000) := by
  have h := checkLog_sound (w := (62382856429 / 312382856429)) (n := 12)
    (lo := (404840147 / 1000000000)) (hi := (101210037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187382856429 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187382856429 / 125000000000) = 1/(125000000000 / 187382856429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6927 : Bounds (404840147 / 1000000000) (101210037 / 250000000) (Real.log (187382856429 / 125000000000)) := by
  have h := reflection_log_6927_neg
  have he : Real.log (187382856429 / 125000000000) = -Real.log (125000000000 / 187382856429) := by
    rw [show ((187382856429 / 125000000000) : ℝ) = ((125000000000 / 187382856429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6928_neg : (45538719 / 250000000) ≤ -Real.log (5000 / 5999) ∧
    -Real.log (5000 / 5999) ≤ (182154877 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 10999)) (n := 12)
    (lo := (45538719 / 250000000)) (hi := (182154877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5999 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5999 / 5000) = 1/(5000 / 5999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6928 : Bounds (45538719 / 250000000) (182154877 / 1000000000) (Real.log (5999 / 5000)) := by
  have h := reflection_log_6928_neg
  have he : Real.log (5999 / 5000) = -Real.log (5000 / 5999) := by
    rw [show ((5999 / 5000) : ℝ) = ((5000 / 5999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6929_neg : (111446791 / 500000000) ≤ -Real.log (4001 / 5000) ∧
    -Real.log (4001 / 5000) ≤ (222893583 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 9001)) (n := 12)
    (lo := (111446791 / 500000000)) (hi := (222893583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4001) = 1/(4001 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6929 : Bounds (-222893583 / 1000000000) (-111446791 / 500000000) (Real.log (4001 / 5000)) := by
  have h := reflection_log_6929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6930_neg : (9989 / 50000000) ≤ -Real.log (5000000 / 5000999) ∧
    -Real.log (5000000 / 5000999) ≤ (199781 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 10000999)) (n := 12)
    (lo := (9989 / 50000000)) (hi := (199781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000999 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000999 / 5000000) = 1/(5000000 / 5000999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6930 : Bounds (9989 / 50000000) (199781 / 1000000000) (Real.log (5000999 / 5000000)) := by
  have h := reflection_log_6930_neg
  have he : Real.log (5000999 / 5000000) = -Real.log (5000000 / 5000999) := by
    rw [show ((5000999 / 5000000) : ℝ) = ((5000000 / 5000999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6931_neg : (199819 / 1000000000) ≤ -Real.log (4999001 / 5000000) ∧
    -Real.log (4999001 / 5000000) ≤ (9991 / 50000000) := by
  have h := checkLog_sound (w := (999 / 9999001)) (n := 12)
    (lo := (199819 / 1000000000)) (hi := (9991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999001) = 1/(4999001 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6931 : Bounds (-9991 / 50000000) (-199819 / 1000000000) (Real.log (4999001 / 5000000)) := by
  have h := reflection_log_6931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6932_neg : (47871861 / 500000000) ≤ -Real.log (1000000 / 1100477) ∧
    -Real.log (1000000 / 1100477) ≤ (95743723 / 1000000000) := by
  have h := checkLog_sound (w := (100477 / 2100477)) (n := 12)
    (lo := (47871861 / 500000000)) (hi := (95743723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100477 / 1000000) = 1/(1000000 / 1100477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6932 : Bounds (47871861 / 500000000) (95743723 / 1000000000) (Real.log (1100477 / 1000000)) := by
  have h := reflection_log_6932_neg
  have he : Real.log (1100477 / 1000000) = -Real.log (1000000 / 1100477) := by
    rw [show ((1100477 / 1000000) : ℝ) = ((1000000 / 1100477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6933_neg : (3309083 / 31250000) ≤ -Real.log (899523 / 1000000) ∧
    -Real.log (899523 / 1000000) ≤ (105890657 / 1000000000) := by
  have h := checkLog_sound (w := (100477 / 1899523)) (n := 12)
    (lo := (3309083 / 31250000)) (hi := (105890657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899523) = 1/(899523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6933 : Bounds (-105890657 / 1000000000) (-3309083 / 31250000) (Real.log (899523 / 1000000)) := by
  have h := reflection_log_6933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6934_neg : (9597087 / 100000000) ≤ -Real.log (1000000 / 1100727) ∧
    -Real.log (1000000 / 1100727) ≤ (95970871 / 1000000000) := by
  have h := checkLog_sound (w := (100727 / 2100727)) (n := 12)
    (lo := (9597087 / 100000000)) (hi := (95970871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100727 / 1000000) = 1/(1000000 / 1100727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6934 : Bounds (9597087 / 100000000) (95970871 / 1000000000) (Real.log (1100727 / 1000000)) := by
  have h := reflection_log_6934_neg
  have he : Real.log (1100727 / 1000000) = -Real.log (1000000 / 1100727) := by
    rw [show ((1100727 / 1000000) : ℝ) = ((1000000 / 1100727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6935_neg : (106168619 / 1000000000) ≤ -Real.log (899273 / 1000000) ∧
    -Real.log (899273 / 1000000) ≤ (5308431 / 50000000) := by
  have h := checkLog_sound (w := (100727 / 1899273)) (n := 12)
    (lo := (106168619 / 1000000000)) (hi := (5308431 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899273) = 1/(899273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6935 : Bounds (-5308431 / 50000000) (-106168619 / 1000000000) (Real.log (899273 / 1000000)) := by
  have h := reflection_log_6935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6936_neg : (10197749 / 1000000000) ≤ -Real.log (989854071471 / 1000000000000) ∧
    -Real.log (989854071471 / 1000000000000) ≤ (40791 / 4000000) := by
  have h := checkLog_sound (w := (10145928529 / 1989854071471)) (n := 12)
    (lo := (10197749 / 1000000000)) (hi := (40791 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989854071471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989854071471) = 1/(989854071471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6936 : Bounds (-40791 / 4000000) (-10197749 / 1000000000) (Real.log (989854071471 / 1000000000000)) := by
  have h := reflection_log_6936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6937_neg : (10146933 / 1000000000) ≤ -Real.log (989904372471 / 1000000000000) ∧
    -Real.log (989904372471 / 1000000000000) ≤ (5073467 / 500000000) := by
  have h := checkLog_sound (w := (10095627529 / 1989904372471)) (n := 12)
    (lo := (10146933 / 1000000000)) (hi := (5073467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989904372471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989904372471) = 1/(989904372471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6937 : Bounds (-5073467 / 500000000) (-10146933 / 1000000000) (Real.log (989904372471 / 1000000000000)) := by
  have h := reflection_log_6937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6938_neg : (100817189 / 500000000) ≤ -Real.log (125000000000 / 152925078069) ∧
    -Real.log (125000000000 / 152925078069) ≤ (201634379 / 1000000000) := by
  have h := checkLog_sound (w := (27925078069 / 277925078069)) (n := 12)
    (lo := (100817189 / 500000000)) (hi := (201634379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152925078069 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152925078069 / 125000000000) = 1/(125000000000 / 152925078069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6938 : Bounds (100817189 / 500000000) (201634379 / 1000000000) (Real.log (152925078069 / 125000000000)) := by
  have h := reflection_log_6938_neg
  have he : Real.log (152925078069 / 125000000000) = -Real.log (125000000000 / 152925078069) := by
    rw [show ((152925078069 / 125000000000) : ℝ) = ((125000000000 / 152925078069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6939_neg : (20213949 / 100000000) ≤ -Real.log (500000000000 / 612009367567) ∧
    -Real.log (500000000000 / 612009367567) ≤ (202139491 / 1000000000) := by
  have h := checkLog_sound (w := (112009367567 / 1112009367567)) (n := 12)
    (lo := (20213949 / 100000000)) (hi := (202139491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612009367567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612009367567 / 500000000000) = 1/(500000000000 / 612009367567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6939 : Bounds (20213949 / 100000000) (202139491 / 1000000000) (Real.log (612009367567 / 500000000000)) := by
  have h := reflection_log_6939_neg
  have he : Real.log (612009367567 / 500000000000) = -Real.log (500000000000 / 612009367567) := by
    rw [show ((612009367567 / 500000000000) : ℝ) = ((500000000000 / 612009367567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6940_neg : (404840147 / 1000000000) ≤ -Real.log (100000000000 / 149906285143) ∧
    -Real.log (100000000000 / 149906285143) ≤ (101210037 / 250000000) := by
  have h := checkLog_sound (w := (49906285143 / 249906285143)) (n := 12)
    (lo := (404840147 / 1000000000)) (hi := (101210037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149906285143 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149906285143 / 100000000000) = 1/(100000000000 / 149906285143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6940 : Bounds (404840147 / 1000000000) (101210037 / 250000000) (Real.log (149906285143 / 100000000000)) := by
  have h := reflection_log_6940_neg
  have he : Real.log (149906285143 / 100000000000) = -Real.log (100000000000 / 149906285143) := by
    rw [show ((149906285143 / 100000000000) : ℝ) = ((100000000000 / 149906285143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6941_neg : (202524229 / 500000000) ≤ -Real.log (250000000000 / 374843789053) ∧
    -Real.log (250000000000 / 374843789053) ≤ (405048459 / 1000000000) := by
  have h := checkLog_sound (w := (124843789053 / 624843789053)) (n := 12)
    (lo := (202524229 / 500000000)) (hi := (405048459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374843789053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374843789053 / 250000000000) = 1/(250000000000 / 374843789053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6941 : Bounds (202524229 / 500000000) (405048459 / 1000000000) (Real.log (374843789053 / 250000000000)) := by
  have h := reflection_log_6941_neg
  have he : Real.log (374843789053 / 250000000000) = -Real.log (250000000000 / 374843789053) := by
    rw [show ((374843789053 / 250000000000) : ℝ) = ((250000000000 / 374843789053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6942_neg : (182238219 / 1000000000) ≤ -Real.log (10000 / 11999) ∧
    -Real.log (10000 / 11999) ≤ (9111911 / 50000000) := by
  have h := checkLog_sound (w := (1999 / 21999)) (n := 12)
    (lo := (182238219 / 1000000000)) (hi := (9111911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11999 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11999 / 10000) = 1/(10000 / 11999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6942 : Bounds (182238219 / 1000000000) (9111911 / 50000000) (Real.log (11999 / 10000)) := by
  have h := reflection_log_6942_neg
  have he : Real.log (11999 / 10000) = -Real.log (10000 / 11999) := by
    rw [show ((11999 / 10000) : ℝ) = ((10000 / 11999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6943_neg : (223018559 / 1000000000) ≤ -Real.log (8001 / 10000) ∧
    -Real.log (8001 / 10000) ≤ (696933 / 3125000) := by
  have h := checkLog_sound (w := (1999 / 18001)) (n := 12)
    (lo := (223018559 / 1000000000)) (hi := (696933 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8001) = 1/(8001 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6943 : Bounds (-696933 / 3125000) (-223018559 / 1000000000) (Real.log (8001 / 10000)) := by
  have h := reflection_log_6943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6944_neg : (4997 / 25000000) ≤ -Real.log (10000000 / 10001999) ∧
    -Real.log (10000000 / 10001999) ≤ (199881 / 1000000000) := by
  have h := checkLog_sound (w := (1999 / 20001999)) (n := 12)
    (lo := (4997 / 25000000)) (hi := (199881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001999 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001999 / 10000000) = 1/(10000000 / 10001999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6944 : Bounds (4997 / 25000000) (199881 / 1000000000) (Real.log (10001999 / 10000000)) := by
  have h := reflection_log_6944_neg
  have he : Real.log (10001999 / 10000000) = -Real.log (10000000 / 10001999) := by
    rw [show ((10001999 / 10000000) : ℝ) = ((10000000 / 10001999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6945_neg : (199919 / 1000000000) ≤ -Real.log (9998001 / 10000000) ∧
    -Real.log (9998001 / 10000000) ≤ (2499 / 12500000) := by
  have h := checkLog_sound (w := (1999 / 19998001)) (n := 12)
    (lo := (199919 / 1000000000)) (hi := (2499 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998001) = 1/(9998001 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6945 : Bounds (-2499 / 12500000) (-199919 / 1000000000) (Real.log (9998001 / 10000000)) := by
  have h := reflection_log_6945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6946_neg : (5986879 / 62500000) ≤ -Real.log (62500 / 68783) ∧
    -Real.log (62500 / 68783) ≤ (19158013 / 200000000) := by
  have h := checkLog_sound (w := (6283 / 131283)) (n := 12)
    (lo := (5986879 / 62500000)) (hi := (19158013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68783 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68783 / 62500) = 1/(62500 / 68783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6946 : Bounds (5986879 / 62500000) (19158013 / 200000000) (Real.log (68783 / 62500)) := by
  have h := reflection_log_6946_neg
  have he : Real.log (68783 / 62500) = -Real.log (62500 / 68783) := by
    rw [show ((68783 / 62500) : ℝ) = ((62500 / 68783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6947_neg : (52973677 / 500000000) ≤ -Real.log (56217 / 62500) ∧
    -Real.log (56217 / 62500) ≤ (21189471 / 200000000) := by
  have h := checkLog_sound (w := (6283 / 118717)) (n := 12)
    (lo := (52973677 / 500000000)) (hi := (21189471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56217) = 1/(56217 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6947 : Bounds (-21189471 / 200000000) (-52973677 / 500000000) (Real.log (56217 / 62500)) := by
  have h := reflection_log_6947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6948_neg : (9601811 / 100000000) ≤ -Real.log (1000000 / 1100779) ∧
    -Real.log (1000000 / 1100779) ≤ (96018111 / 1000000000) := by
  have h := checkLog_sound (w := (100779 / 2100779)) (n := 12)
    (lo := (9601811 / 100000000)) (hi := (96018111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100779 / 1000000) = 1/(1000000 / 1100779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6948 : Bounds (9601811 / 100000000) (96018111 / 1000000000) (Real.log (1100779 / 1000000)) := by
  have h := reflection_log_6948_neg
  have he : Real.log (1100779 / 1000000) = -Real.log (1000000 / 1100779) := by
    rw [show ((1100779 / 1000000) : ℝ) = ((1000000 / 1100779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6949_neg : (53113223 / 500000000) ≤ -Real.log (899221 / 1000000) ∧
    -Real.log (899221 / 1000000) ≤ (106226447 / 1000000000) := by
  have h := checkLog_sound (w := (100779 / 1899221)) (n := 12)
    (lo := (53113223 / 500000000)) (hi := (106226447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899221) = 1/(899221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6949 : Bounds (-106226447 / 1000000000) (-53113223 / 500000000) (Real.log (899221 / 1000000)) := by
  have h := reflection_log_6949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6950_neg : (2041667 / 200000000) ≤ -Real.log (989843593159 / 1000000000000) ∧
    -Real.log (989843593159 / 1000000000000) ≤ (638021 / 62500000) := by
  have h := checkLog_sound (w := (10156406841 / 1989843593159)) (n := 12)
    (lo := (2041667 / 200000000)) (hi := (638021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989843593159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989843593159) = 1/(989843593159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6950 : Bounds (-638021 / 62500000) (-2041667 / 200000000) (Real.log (989843593159 / 1000000000000)) := by
  have h := reflection_log_6950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6951_neg : (10157289 / 1000000000) ≤ -Real.log (3866773911 / 3906250000) ∧
    -Real.log (3866773911 / 3906250000) ≤ (1015729 / 100000000) := by
  have h := checkLog_sound (w := (39476089 / 7773023911)) (n := 12)
    (lo := (10157289 / 1000000000)) (hi := (1015729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3866773911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3866773911) = 1/(3866773911 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6951 : Bounds (-1015729 / 100000000) (-10157289 / 1000000000) (Real.log (3866773911 / 3906250000)) := by
  have h := reflection_log_6951_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6952_neg : (201737419 / 1000000000) ≤ -Real.log (500000000000 / 611763345607) ∧
    -Real.log (500000000000 / 611763345607) ≤ (10086871 / 50000000) := by
  have h := checkLog_sound (w := (111763345607 / 1111763345607)) (n := 12)
    (lo := (201737419 / 1000000000)) (hi := (10086871 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611763345607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611763345607 / 500000000000) = 1/(500000000000 / 611763345607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6952 : Bounds (201737419 / 1000000000) (10086871 / 50000000) (Real.log (611763345607 / 500000000000)) := by
  have h := reflection_log_6952_neg
  have he : Real.log (611763345607 / 500000000000) = -Real.log (500000000000 / 611763345607) := by
    rw [show ((611763345607 / 500000000000) : ℝ) = ((500000000000 / 611763345607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6953_neg : (202244557 / 1000000000) ≤ -Real.log (500000000000 / 612073672657) ∧
    -Real.log (500000000000 / 612073672657) ≤ (101122279 / 500000000) := by
  have h := checkLog_sound (w := (112073672657 / 1112073672657)) (n := 12)
    (lo := (202244557 / 1000000000)) (hi := (101122279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612073672657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612073672657 / 500000000000) = 1/(500000000000 / 612073672657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6953 : Bounds (202244557 / 1000000000) (101122279 / 500000000) (Real.log (612073672657 / 500000000000)) := by
  have h := reflection_log_6953_neg
  have he : Real.log (612073672657 / 500000000000) = -Real.log (500000000000 / 612073672657) := by
    rw [show ((612073672657 / 500000000000) : ℝ) = ((500000000000 / 612073672657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6954_neg : (202524229 / 500000000) ≤ -Real.log (100000000000 / 149937515621) ∧
    -Real.log (100000000000 / 149937515621) ≤ (405048459 / 1000000000) := by
  have h := checkLog_sound (w := (49937515621 / 249937515621)) (n := 12)
    (lo := (202524229 / 500000000)) (hi := (405048459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149937515621 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149937515621 / 100000000000) = 1/(100000000000 / 149937515621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6954 : Bounds (202524229 / 500000000) (405048459 / 1000000000) (Real.log (149937515621 / 100000000000)) := by
  have h := reflection_log_6954_neg
  have he : Real.log (149937515621 / 100000000000) = -Real.log (100000000000 / 149937515621) := by
    rw [show ((149937515621 / 100000000000) : ℝ) = ((100000000000 / 149937515621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6955_neg : (405256779 / 1000000000) ≤ -Real.log (500000000000 / 749843769529) ∧
    -Real.log (500000000000 / 749843769529) ≤ (20262839 / 50000000) := by
  have h := checkLog_sound (w := (249843769529 / 1249843769529)) (n := 12)
    (lo := (405256779 / 1000000000)) (hi := (20262839 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749843769529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749843769529 / 500000000000) = 1/(500000000000 / 749843769529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6955 : Bounds (405256779 / 1000000000) (20262839 / 50000000) (Real.log (749843769529 / 500000000000)) := by
  have h := reflection_log_6955_neg
  have he : Real.log (749843769529 / 500000000000) = -Real.log (500000000000 / 749843769529) := by
    rw [show ((749843769529 / 500000000000) : ℝ) = ((500000000000 / 749843769529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6956_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6956 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_6956_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6957_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
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


theorem reflection_log_6957 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_6957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6958_neg : (9999 / 50000000) ≤ -Real.log (5000 / 5001) ∧
    -Real.log (5000 / 5001) ≤ (199981 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 10001)) (n := 12)
    (lo := (9999 / 50000000)) (hi := (199981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5001 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5001 / 5000) = 1/(5000 / 5001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6958 : Bounds (9999 / 50000000) (199981 / 1000000000) (Real.log (5001 / 5000)) := by
  have h := reflection_log_6958_neg
  have he : Real.log (5001 / 5000) = -Real.log (5000 / 5001) := by
    rw [show ((5001 / 5000) : ℝ) = ((5000 / 5001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6959_neg : (10001 / 50000000) ≤ -Real.log (4999 / 5000) ∧
    -Real.log (4999 / 5000) ≤ (200021 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9999)) (n := 12)
    (lo := (10001 / 50000000)) (hi := (200021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4999) = 1/(4999 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6959 : Bounds (-200021 / 1000000000) (-10001 / 50000000) (Real.log (4999 / 5000)) := by
  have h := reflection_log_6959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6960_neg : (23959101 / 250000000) ≤ -Real.log (1000000 / 1100579) ∧
    -Real.log (1000000 / 1100579) ≤ (19167281 / 200000000) := by
  have h := checkLog_sound (w := (100579 / 2100579)) (n := 12)
    (lo := (23959101 / 250000000)) (hi := (19167281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100579 / 1000000) = 1/(1000000 / 1100579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6960 : Bounds (23959101 / 250000000) (19167281 / 200000000) (Real.log (1100579 / 1000000)) := by
  have h := reflection_log_6960_neg
  have he : Real.log (1100579 / 1000000) = -Real.log (1000000 / 1100579) := by
    rw [show ((1100579 / 1000000) : ℝ) = ((1000000 / 1100579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6961_neg : (13250507 / 125000000) ≤ -Real.log (899421 / 1000000) ∧
    -Real.log (899421 / 1000000) ≤ (106004057 / 1000000000) := by
  have h := checkLog_sound (w := (100579 / 1899421)) (n := 12)
    (lo := (13250507 / 125000000)) (hi := (106004057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899421) = 1/(899421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6961 : Bounds (-106004057 / 1000000000) (-13250507 / 125000000) (Real.log (899421 / 1000000)) := by
  have h := reflection_log_6961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6962_neg : (2401611 / 25000000) ≤ -Real.log (100000 / 110083) ∧
    -Real.log (100000 / 110083) ≤ (96064441 / 1000000000) := by
  have h := checkLog_sound (w := (10083 / 210083)) (n := 12)
    (lo := (2401611 / 25000000)) (hi := (96064441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110083 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110083 / 100000) = 1/(100000 / 110083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6962 : Bounds (2401611 / 25000000) (96064441 / 1000000000) (Real.log (110083 / 100000)) := by
  have h := reflection_log_6962_neg
  have he : Real.log (110083 / 100000) = -Real.log (100000 / 110083) := by
    rw [show ((110083 / 100000) : ℝ) = ((100000 / 110083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6963_neg : (106283163 / 1000000000) ≤ -Real.log (89917 / 100000) ∧
    -Real.log (89917 / 100000) ≤ (26570791 / 250000000) := by
  have h := checkLog_sound (w := (10083 / 189917)) (n := 12)
    (lo := (106283163 / 1000000000)) (hi := (26570791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89917) = 1/(89917 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6963 : Bounds (-26570791 / 250000000) (-106283163 / 1000000000) (Real.log (89917 / 100000)) := by
  have h := reflection_log_6963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6964_neg : (5109361 / 500000000) ≤ -Real.log (9898333111 / 10000000000) ∧
    -Real.log (9898333111 / 10000000000) ≤ (10218723 / 1000000000) := by
  have h := checkLog_sound (w := (101666889 / 19898333111)) (n := 12)
    (lo := (5109361 / 500000000)) (hi := (10218723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9898333111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9898333111) = 1/(9898333111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6964 : Bounds (-10218723 / 1000000000) (-5109361 / 500000000) (Real.log (9898333111 / 10000000000)) := by
  have h := reflection_log_6964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6965_neg : (10167651 / 1000000000) ≤ -Real.log (989883864759 / 1000000000000) ∧
    -Real.log (989883864759 / 1000000000000) ≤ (2541913 / 250000000) := by
  have h := checkLog_sound (w := (10116135241 / 1989883864759)) (n := 12)
    (lo := (10167651 / 1000000000)) (hi := (2541913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989883864759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989883864759) = 1/(989883864759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6965 : Bounds (-2541913 / 250000000) (-10167651 / 1000000000) (Real.log (989883864759 / 1000000000000)) := by
  have h := reflection_log_6965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6966_neg : (10092023 / 50000000) ≤ -Real.log (250000000000 / 305913193043) ∧
    -Real.log (250000000000 / 305913193043) ≤ (201840461 / 1000000000) := by
  have h := checkLog_sound (w := (55913193043 / 555913193043)) (n := 12)
    (lo := (10092023 / 50000000)) (hi := (201840461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305913193043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305913193043 / 250000000000) = 1/(250000000000 / 305913193043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6966 : Bounds (10092023 / 50000000) (201840461 / 1000000000) (Real.log (305913193043 / 250000000000)) := by
  have h := reflection_log_6966_neg
  have he : Real.log (305913193043 / 250000000000) = -Real.log (250000000000 / 305913193043) := by
    rw [show ((305913193043 / 250000000000) : ℝ) = ((250000000000 / 305913193043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6967_neg : (50586901 / 250000000) ≤ -Real.log (100000000000 / 122427349667) ∧
    -Real.log (100000000000 / 122427349667) ≤ (40469521 / 200000000) := by
  have h := checkLog_sound (w := (22427349667 / 222427349667)) (n := 12)
    (lo := (50586901 / 250000000)) (hi := (40469521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122427349667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122427349667 / 100000000000) = 1/(100000000000 / 122427349667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6967 : Bounds (50586901 / 250000000) (40469521 / 200000000) (Real.log (122427349667 / 100000000000)) := by
  have h := reflection_log_6967_neg
  have he : Real.log (122427349667 / 100000000000) = -Real.log (100000000000 / 122427349667) := by
    rw [show ((122427349667 / 100000000000) : ℝ) = ((100000000000 / 122427349667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6968_neg : (405256779 / 1000000000) ≤ -Real.log (62500000000 / 93730471191) ∧
    -Real.log (62500000000 / 93730471191) ≤ (20262839 / 50000000) := by
  have h := checkLog_sound (w := (31230471191 / 156230471191)) (n := 12)
    (lo := (405256779 / 1000000000)) (hi := (20262839 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93730471191 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93730471191 / 62500000000) = 1/(62500000000 / 93730471191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6968 : Bounds (405256779 / 1000000000) (20262839 / 50000000) (Real.log (93730471191 / 62500000000)) := by
  have h := reflection_log_6968_neg
  have he : Real.log (93730471191 / 62500000000) = -Real.log (62500000000 / 93730471191) := by
    rw [show ((93730471191 / 62500000000) : ℝ) = ((62500000000 / 93730471191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6969_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6969 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_6969_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6970_neg : (22842267 / 125000000) ≤ -Real.log (2000 / 2401) ∧
    -Real.log (2000 / 2401) ≤ (182738137 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 4401)) (n := 12)
    (lo := (22842267 / 125000000)) (hi := (182738137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 2000) = 1/(2000 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6970 : Bounds (22842267 / 125000000) (182738137 / 1000000000) (Real.log (2401 / 2000)) := by
  have h := reflection_log_6970_neg
  have he : Real.log (2401 / 2000) = -Real.log (2000 / 2401) := by
    rw [show ((2401 / 2000) : ℝ) = ((2000 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6971_neg : (111884373 / 500000000) ≤ -Real.log (1599 / 2000) ∧
    -Real.log (1599 / 2000) ≤ (223768747 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 3599)) (n := 12)
    (lo := (111884373 / 500000000)) (hi := (223768747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1599) = 1/(1599 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6971 : Bounds (-223768747 / 1000000000) (-111884373 / 500000000) (Real.log (1599 / 2000)) := by
  have h := reflection_log_6971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6972_neg : (200479 / 1000000000) ≤ -Real.log (2000000 / 2000401) ∧
    -Real.log (2000000 / 2000401) ≤ (1253 / 6250000) := by
  have h := checkLog_sound (w := (401 / 4000401)) (n := 12)
    (lo := (200479 / 1000000000)) (hi := (1253 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000401 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000401 / 2000000) = 1/(2000000 / 2000401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6972 : Bounds (200479 / 1000000000) (1253 / 6250000) (Real.log (2000401 / 2000000)) := by
  have h := reflection_log_6972_neg
  have he : Real.log (2000401 / 2000000) = -Real.log (2000000 / 2000401) := by
    rw [show ((2000401 / 2000000) : ℝ) = ((2000000 / 2000401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6973_neg : (5013 / 25000000) ≤ -Real.log (1999599 / 2000000) ∧
    -Real.log (1999599 / 2000000) ≤ (200521 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 3999599)) (n := 12)
    (lo := (5013 / 25000000)) (hi := (200521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999599) = 1/(1999599 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6973 : Bounds (-200521 / 1000000000) (-5013 / 25000000) (Real.log (1999599 / 2000000)) := by
  have h := reflection_log_6973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6974_neg : (95882743 / 1000000000) ≤ -Real.log (100000 / 110063) ∧
    -Real.log (100000 / 110063) ≤ (11985343 / 125000000) := by
  have h := checkLog_sound (w := (10063 / 210063)) (n := 12)
    (lo := (95882743 / 1000000000)) (hi := (11985343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110063 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110063 / 100000) = 1/(100000 / 110063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6974 : Bounds (95882743 / 1000000000) (11985343 / 125000000) (Real.log (110063 / 100000)) := by
  have h := reflection_log_6974_neg
  have he : Real.log (110063 / 100000) = -Real.log (100000 / 110063) := by
    rw [show ((110063 / 100000) : ℝ) = ((100000 / 110063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6975_neg : (2651519 / 25000000) ≤ -Real.log (89937 / 100000) ∧
    -Real.log (89937 / 100000) ≤ (106060761 / 1000000000) := by
  have h := checkLog_sound (w := (10063 / 189937)) (n := 12)
    (lo := (2651519 / 25000000)) (hi := (106060761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89937) = 1/(89937 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6975 : Bounds (-106060761 / 1000000000) (-2651519 / 25000000) (Real.log (89937 / 100000)) := by
  have h := reflection_log_6975_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


