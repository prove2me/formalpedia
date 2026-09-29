-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0086__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0086__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:01:10.493436+00:00
-- url     : https://prove2.me/theorems/3c03f44b-298b-4df3-9128-547db9fbaff3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0086 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0087)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0086 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0087)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0086 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0087)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0086 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0087) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0086 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0087).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0086 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5504_neg : (91005473 / 1000000000) ≤ -Real.log (40000 / 43811) ∧
    -Real.log (40000 / 43811) ≤ (45502737 / 500000000) := by
  have h := checkLog_sound (w := (3811 / 83811)) (n := 12)
    (lo := (91005473 / 1000000000)) (hi := (45502737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43811 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43811 / 40000) = 1/(40000 / 43811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5504 : Bounds (91005473 / 1000000000) (45502737 / 500000000) (Real.log (43811 / 40000)) := by
  have h := reflection_log_5504_neg
  have he : Real.log (43811 / 40000) = -Real.log (40000 / 43811) := by
    rw [show ((43811 / 40000) : ℝ) = ((40000 / 43811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5505_neg : (12515531 / 125000000) ≤ -Real.log (36189 / 40000) ∧
    -Real.log (36189 / 40000) ≤ (100124249 / 1000000000) := by
  have h := checkLog_sound (w := (3811 / 76189)) (n := 12)
    (lo := (12515531 / 125000000)) (hi := (100124249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36189) = 1/(36189 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5505 : Bounds (-100124249 / 1000000000) (-12515531 / 125000000) (Real.log (36189 / 40000)) := by
  have h := reflection_log_5505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5506_neg : (18245097 / 200000000) ≤ -Real.log (250000 / 273879) ∧
    -Real.log (250000 / 273879) ≤ (45612743 / 500000000) := by
  have h := checkLog_sound (w := (23879 / 523879)) (n := 12)
    (lo := (18245097 / 200000000)) (hi := (45612743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273879 / 250000) = 1/(250000 / 273879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5506 : Bounds (18245097 / 200000000) (45612743 / 500000000) (Real.log (273879 / 250000)) := by
  have h := reflection_log_5506_neg
  have he : Real.log (273879 / 250000) = -Real.log (250000 / 273879) := by
    rw [show ((273879 / 250000) : ℝ) = ((250000 / 273879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5507_neg : (100390663 / 1000000000) ≤ -Real.log (226121 / 250000) ∧
    -Real.log (226121 / 250000) ≤ (12548833 / 125000000) := by
  have h := checkLog_sound (w := (23879 / 476121)) (n := 12)
    (lo := (100390663 / 1000000000)) (hi := (12548833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226121) = 1/(226121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5507 : Bounds (-12548833 / 125000000) (-100390663 / 1000000000) (Real.log (226121 / 250000)) := by
  have h := reflection_log_5507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5508_neg : (4582589 / 500000000) ≤ -Real.log (61929793359 / 62500000000) ∧
    -Real.log (61929793359 / 62500000000) ≤ (9165179 / 1000000000) := by
  have h := checkLog_sound (w := (570206641 / 124429793359)) (n := 12)
    (lo := (4582589 / 500000000)) (hi := (9165179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61929793359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61929793359) = 1/(61929793359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5508 : Bounds (-9165179 / 1000000000) (-4582589 / 500000000) (Real.log (61929793359 / 62500000000)) := by
  have h := reflection_log_5508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5509_neg : (364751 / 40000000) ≤ -Real.log (1585476279 / 1600000000) ∧
    -Real.log (1585476279 / 1600000000) ≤ (1139847 / 125000000) := by
  have h := checkLog_sound (w := (14523721 / 3185476279)) (n := 12)
    (lo := (364751 / 40000000)) (hi := (1139847 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1585476279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1585476279) = 1/(1585476279 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5509 : Bounds (-1139847 / 125000000) (-364751 / 40000000) (Real.log (1585476279 / 1600000000)) := by
  have h := reflection_log_5509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5510_neg : (95564861 / 500000000) ≤ -Real.log (125000000000 / 151327060709) ∧
    -Real.log (125000000000 / 151327060709) ≤ (191129723 / 1000000000) := by
  have h := checkLog_sound (w := (26327060709 / 276327060709)) (n := 12)
    (lo := (95564861 / 500000000)) (hi := (191129723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151327060709 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151327060709 / 125000000000) = 1/(125000000000 / 151327060709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5510 : Bounds (95564861 / 500000000) (191129723 / 1000000000) (Real.log (151327060709 / 125000000000)) := by
  have h := reflection_log_5510_neg
  have he : Real.log (151327060709 / 125000000000) = -Real.log (125000000000 / 151327060709) := by
    rw [show ((151327060709 / 125000000000) : ℝ) = ((125000000000 / 151327060709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5511_neg : (47904037 / 250000000) ≤ -Real.log (500000000000 / 605602752509) ∧
    -Real.log (500000000000 / 605602752509) ≤ (191616149 / 1000000000) := by
  have h := checkLog_sound (w := (105602752509 / 1105602752509)) (n := 12)
    (lo := (47904037 / 250000000)) (hi := (191616149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605602752509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605602752509 / 500000000000) = 1/(500000000000 / 605602752509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5511 : Bounds (47904037 / 250000000) (191616149 / 1000000000) (Real.log (605602752509 / 500000000000)) := by
  have h := reflection_log_5511_neg
  have he : Real.log (605602752509 / 500000000000) = -Real.log (500000000000 / 605602752509) := by
    rw [show ((605602752509 / 500000000000) : ℝ) = ((500000000000 / 605602752509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5512_neg : (95909247 / 250000000) ≤ -Real.log (125000000000 / 183451573103) ∧
    -Real.log (125000000000 / 183451573103) ≤ (383636989 / 1000000000) := by
  have h := checkLog_sound (w := (58451573103 / 308451573103)) (n := 12)
    (lo := (95909247 / 250000000)) (hi := (383636989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183451573103 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183451573103 / 125000000000) = 1/(125000000000 / 183451573103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5512 : Bounds (95909247 / 250000000) (383636989 / 1000000000) (Real.log (183451573103 / 125000000000)) := by
  have h := reflection_log_5512_neg
  have he : Real.log (183451573103 / 125000000000) = -Real.log (125000000000 / 183451573103) := by
    rw [show ((183451573103 / 125000000000) : ℝ) = ((125000000000 / 183451573103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5513_neg : (191922221 / 500000000) ≤ -Real.log (250000000000 / 366979269497) ∧
    -Real.log (250000000000 / 366979269497) ≤ (383844443 / 1000000000) := by
  have h := checkLog_sound (w := (116979269497 / 616979269497)) (n := 12)
    (lo := (191922221 / 500000000)) (hi := (383844443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366979269497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366979269497 / 250000000000) = 1/(250000000000 / 366979269497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5513 : Bounds (191922221 / 500000000) (383844443 / 1000000000) (Real.log (366979269497 / 250000000000)) := by
  have h := reflection_log_5513_neg
  have he : Real.log (366979269497 / 250000000000) = -Real.log (250000000000 / 366979269497) := by
    rw [show ((366979269497 / 250000000000) : ℝ) = ((250000000000 / 366979269497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5514_neg : (86850587 / 500000000) ≤ -Real.log (10000 / 11897) ∧
    -Real.log (10000 / 11897) ≤ (6948047 / 40000000) := by
  have h := checkLog_sound (w := (1897 / 21897)) (n := 12)
    (lo := (86850587 / 500000000)) (hi := (6948047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11897 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11897 / 10000) = 1/(10000 / 11897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5514 : Bounds (86850587 / 500000000) (6948047 / 40000000) (Real.log (11897 / 10000)) := by
  have h := reflection_log_5514_neg
  have he : Real.log (11897 / 10000) = -Real.log (10000 / 11897) := by
    rw [show ((11897 / 10000) : ℝ) = ((10000 / 11897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5515_neg : (210350729 / 1000000000) ≤ -Real.log (8103 / 10000) ∧
    -Real.log (8103 / 10000) ≤ (21035073 / 100000000) := by
  have h := checkLog_sound (w := (1897 / 18103)) (n := 12)
    (lo := (210350729 / 1000000000)) (hi := (21035073 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8103) = 1/(8103 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5515 : Bounds (-21035073 / 100000000) (-210350729 / 1000000000) (Real.log (8103 / 10000)) := by
  have h := reflection_log_5515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5516_neg : (94841 / 500000000) ≤ -Real.log (10000000 / 10001897) ∧
    -Real.log (10000000 / 10001897) ≤ (189683 / 1000000000) := by
  have h := checkLog_sound (w := (1897 / 20001897)) (n := 12)
    (lo := (94841 / 500000000)) (hi := (189683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001897 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001897 / 10000000) = 1/(10000000 / 10001897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5516 : Bounds (94841 / 500000000) (189683 / 1000000000) (Real.log (10001897 / 10000000)) := by
  have h := reflection_log_5516_neg
  have he : Real.log (10001897 / 10000000) = -Real.log (10000000 / 10001897) := by
    rw [show ((10001897 / 10000000) : ℝ) = ((10000000 / 10001897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5517_neg : (189717 / 1000000000) ≤ -Real.log (9998103 / 10000000) ∧
    -Real.log (9998103 / 10000000) ≤ (94859 / 500000000) := by
  have h := checkLog_sound (w := (1897 / 19998103)) (n := 12)
    (lo := (189717 / 1000000000)) (hi := (94859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998103) = 1/(9998103 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5517 : Bounds (-94859 / 500000000) (-189717 / 1000000000) (Real.log (9998103 / 10000000)) := by
  have h := reflection_log_5517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5518_neg : (18210407 / 200000000) ≤ -Real.log (500000 / 547663) ∧
    -Real.log (500000 / 547663) ≤ (22763009 / 250000000) := by
  have h := checkLog_sound (w := (47663 / 1047663)) (n := 12)
    (lo := (18210407 / 200000000)) (hi := (22763009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547663 / 500000) = 1/(500000 / 547663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5518 : Bounds (18210407 / 200000000) (22763009 / 250000000) (Real.log (547663 / 500000)) := by
  have h := reflection_log_5518_neg
  have he : Real.log (547663 / 500000) = -Real.log (500000 / 547663) := by
    rw [show ((547663 / 500000) : ℝ) = ((500000 / 547663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5519_neg : (100180621 / 1000000000) ≤ -Real.log (452337 / 500000) ∧
    -Real.log (452337 / 500000) ≤ (50090311 / 500000000) := by
  have h := checkLog_sound (w := (47663 / 952337)) (n := 12)
    (lo := (100180621 / 1000000000)) (hi := (50090311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452337) = 1/(452337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5519 : Bounds (-50090311 / 500000000) (-100180621 / 1000000000) (Real.log (452337 / 500000)) := by
  have h := reflection_log_5519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5520_neg : (91272037 / 1000000000) ≤ -Real.log (1000000 / 1095567) ∧
    -Real.log (1000000 / 1095567) ≤ (45636019 / 500000000) := by
  have h := checkLog_sound (w := (95567 / 2095567)) (n := 12)
    (lo := (91272037 / 1000000000)) (hi := (45636019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095567 / 1000000) = 1/(1000000 / 1095567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5520 : Bounds (91272037 / 1000000000) (45636019 / 500000000) (Real.log (1095567 / 1000000)) := by
  have h := reflection_log_5520_neg
  have he : Real.log (1095567 / 1000000) = -Real.log (1000000 / 1095567) := by
    rw [show ((1095567 / 1000000) : ℝ) = ((1000000 / 1095567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5521_neg : (2008941 / 20000000) ≤ -Real.log (904433 / 1000000) ∧
    -Real.log (904433 / 1000000) ≤ (100447051 / 1000000000) := by
  have h := checkLog_sound (w := (95567 / 1904433)) (n := 12)
    (lo := (2008941 / 20000000)) (hi := (100447051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904433) = 1/(904433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5521 : Bounds (-100447051 / 1000000000) (-2008941 / 20000000) (Real.log (904433 / 1000000)) := by
  have h := reflection_log_5521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5522_neg : (9175013 / 1000000000) ≤ -Real.log (990866948511 / 1000000000000) ∧
    -Real.log (990866948511 / 1000000000000) ≤ (4587507 / 500000000) := by
  have h := checkLog_sound (w := (9133051489 / 1990866948511)) (n := 12)
    (lo := (9175013 / 1000000000)) (hi := (4587507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990866948511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990866948511) = 1/(990866948511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5522 : Bounds (-4587507 / 500000000) (-9175013 / 1000000000) (Real.log (990866948511 / 1000000000000)) := by
  have h := reflection_log_5522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5523_neg : (1825717 / 200000000) ≤ -Real.log (247728238431 / 250000000000) ∧
    -Real.log (247728238431 / 250000000000) ≤ (4564293 / 500000000) := by
  have h := checkLog_sound (w := (2271761569 / 497728238431)) (n := 12)
    (lo := (1825717 / 200000000)) (hi := (4564293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247728238431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247728238431) = 1/(247728238431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5523 : Bounds (-4564293 / 500000000) (-1825717 / 200000000) (Real.log (247728238431 / 250000000000)) := by
  have h := reflection_log_5523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5524_neg : (191232657 / 1000000000) ≤ -Real.log (50000000000 / 60537055337) ∧
    -Real.log (50000000000 / 60537055337) ≤ (95616329 / 500000000) := by
  have h := checkLog_sound (w := (10537055337 / 110537055337)) (n := 12)
    (lo := (191232657 / 1000000000)) (hi := (95616329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60537055337 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60537055337 / 50000000000) = 1/(50000000000 / 60537055337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5524 : Bounds (191232657 / 1000000000) (95616329 / 500000000) (Real.log (60537055337 / 50000000000)) := by
  have h := reflection_log_5524_neg
  have he : Real.log (60537055337 / 50000000000) = -Real.log (50000000000 / 60537055337) := by
    rw [show ((60537055337 / 50000000000) : ℝ) = ((50000000000 / 60537055337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5525_neg : (11982443 / 62500000) ≤ -Real.log (250000000000 / 302832548127) ∧
    -Real.log (250000000000 / 302832548127) ≤ (191719089 / 1000000000) := by
  have h := checkLog_sound (w := (52832548127 / 552832548127)) (n := 12)
    (lo := (11982443 / 62500000)) (hi := (191719089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302832548127 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302832548127 / 250000000000) = 1/(250000000000 / 302832548127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5525 : Bounds (11982443 / 62500000) (191719089 / 1000000000) (Real.log (302832548127 / 250000000000)) := by
  have h := reflection_log_5525_neg
  have he : Real.log (302832548127 / 250000000000) = -Real.log (250000000000 / 302832548127) := by
    rw [show ((302832548127 / 250000000000) : ℝ) = ((250000000000 / 302832548127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5526_neg : (191922221 / 500000000) ≤ -Real.log (500000000000 / 733958538993) ∧
    -Real.log (500000000000 / 733958538993) ≤ (383844443 / 1000000000) := by
  have h := checkLog_sound (w := (233958538993 / 1233958538993)) (n := 12)
    (lo := (191922221 / 500000000)) (hi := (383844443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733958538993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733958538993 / 500000000000) = 1/(500000000000 / 733958538993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5526 : Bounds (191922221 / 500000000) (383844443 / 1000000000) (Real.log (733958538993 / 500000000000)) := by
  have h := reflection_log_5526_neg
  have he : Real.log (733958538993 / 500000000000) = -Real.log (500000000000 / 733958538993) := by
    rw [show ((733958538993 / 500000000000) : ℝ) = ((500000000000 / 733958538993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5527_neg : (6000811 / 15625000) ≤ -Real.log (31250000000 / 45881926447) ∧
    -Real.log (31250000000 / 45881926447) ≤ (76810381 / 200000000) := by
  have h := checkLog_sound (w := (14631926447 / 77131926447)) (n := 12)
    (lo := (6000811 / 15625000)) (hi := (76810381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45881926447 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45881926447 / 31250000000) = 1/(31250000000 / 45881926447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5527 : Bounds (6000811 / 15625000) (76810381 / 200000000) (Real.log (45881926447 / 31250000000)) := by
  have h := reflection_log_5527_neg
  have he : Real.log (45881926447 / 31250000000) = -Real.log (31250000000 / 45881926447) := by
    rw [show ((45881926447 / 31250000000) : ℝ) = ((31250000000 / 45881926447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5528_neg : (6951409 / 40000000) ≤ -Real.log (5000 / 5949) ∧
    -Real.log (5000 / 5949) ≤ (86892613 / 500000000) := by
  have h := checkLog_sound (w := (949 / 10949)) (n := 12)
    (lo := (6951409 / 40000000)) (hi := (86892613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949 / 5000) = 1/(5000 / 5949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5528 : Bounds (6951409 / 40000000) (86892613 / 500000000) (Real.log (5949 / 5000)) := by
  have h := reflection_log_5528_neg
  have he : Real.log (5949 / 5000) = -Real.log (5000 / 5949) := by
    rw [show ((5949 / 5000) : ℝ) = ((5000 / 5949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5529_neg : (52618537 / 250000000) ≤ -Real.log (4051 / 5000) ∧
    -Real.log (4051 / 5000) ≤ (210474149 / 1000000000) := by
  have h := checkLog_sound (w := (949 / 9051)) (n := 12)
    (lo := (52618537 / 250000000)) (hi := (210474149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4051) = 1/(4051 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5529 : Bounds (-210474149 / 1000000000) (-52618537 / 250000000) (Real.log (4051 / 5000)) := by
  have h := reflection_log_5529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5530_neg : (189781 / 1000000000) ≤ -Real.log (5000000 / 5000949) ∧
    -Real.log (5000000 / 5000949) ≤ (94891 / 500000000) := by
  have h := checkLog_sound (w := (949 / 10000949)) (n := 12)
    (lo := (189781 / 1000000000)) (hi := (94891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000949 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000949 / 5000000) = 1/(5000000 / 5000949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5530 : Bounds (189781 / 1000000000) (94891 / 500000000) (Real.log (5000949 / 5000000)) := by
  have h := reflection_log_5530_neg
  have he : Real.log (5000949 / 5000000) = -Real.log (5000000 / 5000949) := by
    rw [show ((5000949 / 5000000) : ℝ) = ((5000000 / 5000949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5531_neg : (94909 / 500000000) ≤ -Real.log (4999051 / 5000000) ∧
    -Real.log (4999051 / 5000000) ≤ (189819 / 1000000000) := by
  have h := checkLog_sound (w := (949 / 9999051)) (n := 12)
    (lo := (94909 / 500000000)) (hi := (189819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999051) = 1/(4999051 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5531 : Bounds (-189819 / 1000000000) (-94909 / 500000000) (Real.log (4999051 / 5000000)) := by
  have h := reflection_log_5531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5532_neg : (22774649 / 250000000) ≤ -Real.log (1000000 / 1095377) ∧
    -Real.log (1000000 / 1095377) ≤ (91098597 / 1000000000) := by
  have h := checkLog_sound (w := (95377 / 2095377)) (n := 12)
    (lo := (22774649 / 250000000)) (hi := (91098597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095377 / 1000000) = 1/(1000000 / 1095377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5532 : Bounds (22774649 / 250000000) (91098597 / 1000000000) (Real.log (1095377 / 1000000)) := by
  have h := reflection_log_5532_neg
  have he : Real.log (1095377 / 1000000) = -Real.log (1000000 / 1095377) := by
    rw [show ((1095377 / 1000000) : ℝ) = ((1000000 / 1095377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5533_neg : (25059249 / 250000000) ≤ -Real.log (904623 / 1000000) ∧
    -Real.log (904623 / 1000000) ≤ (100236997 / 1000000000) := by
  have h := checkLog_sound (w := (95377 / 1904623)) (n := 12)
    (lo := (25059249 / 250000000)) (hi := (100236997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904623) = 1/(904623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5533 : Bounds (-100236997 / 1000000000) (-25059249 / 250000000) (Real.log (904623 / 1000000)) := by
  have h := reflection_log_5533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5534_neg : (91318587 / 1000000000) ≤ -Real.log (500000 / 547809) ∧
    -Real.log (500000 / 547809) ≤ (22829647 / 250000000) := by
  have h := checkLog_sound (w := (47809 / 1047809)) (n := 12)
    (lo := (91318587 / 1000000000)) (hi := (22829647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547809 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547809 / 500000) = 1/(500000 / 547809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5534 : Bounds (91318587 / 1000000000) (22829647 / 250000000) (Real.log (547809 / 500000)) := by
  have h := reflection_log_5534_neg
  have he : Real.log (547809 / 500000) = -Real.log (500000 / 547809) := by
    rw [show ((547809 / 500000) : ℝ) = ((500000 / 547809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5535_neg : (100503441 / 1000000000) ≤ -Real.log (452191 / 500000) ∧
    -Real.log (452191 / 500000) ≤ (50251721 / 500000000) := by
  have h := checkLog_sound (w := (47809 / 952191)) (n := 12)
    (lo := (100503441 / 1000000000)) (hi := (50251721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452191) = 1/(452191 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5535 : Bounds (-50251721 / 500000000) (-100503441 / 1000000000) (Real.log (452191 / 500000)) := by
  have h := reflection_log_5535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5536_neg : (9184853 / 1000000000) ≤ -Real.log (247714299519 / 250000000000) ∧
    -Real.log (247714299519 / 250000000000) ≤ (4592427 / 500000000) := by
  have h := checkLog_sound (w := (2285700481 / 497714299519)) (n := 12)
    (lo := (9184853 / 1000000000)) (hi := (4592427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247714299519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247714299519) = 1/(247714299519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5536 : Bounds (-4592427 / 500000000) (-9184853 / 1000000000) (Real.log (247714299519 / 250000000000)) := by
  have h := reflection_log_5536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5537_neg : (11423 / 1250000) ≤ -Real.log (990903227871 / 1000000000000) ∧
    -Real.log (990903227871 / 1000000000000) ≤ (9138401 / 1000000000) := by
  have h := checkLog_sound (w := (9096772129 / 1990903227871)) (n := 12)
    (lo := (11423 / 1250000)) (hi := (9138401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990903227871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990903227871) = 1/(990903227871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5537 : Bounds (-9138401 / 1000000000) (-11423 / 1250000) (Real.log (990903227871 / 1000000000000)) := by
  have h := reflection_log_5537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5538_neg : (23916949 / 125000000) ≤ -Real.log (50000000000 / 60543287093) ∧
    -Real.log (50000000000 / 60543287093) ≤ (191335593 / 1000000000) := by
  have h := checkLog_sound (w := (10543287093 / 110543287093)) (n := 12)
    (lo := (23916949 / 125000000)) (hi := (191335593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60543287093 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60543287093 / 50000000000) = 1/(50000000000 / 60543287093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5538 : Bounds (23916949 / 125000000) (191335593 / 1000000000) (Real.log (60543287093 / 50000000000)) := by
  have h := reflection_log_5538_neg
  have he : Real.log (60543287093 / 50000000000) = -Real.log (50000000000 / 60543287093) := by
    rw [show ((60543287093 / 50000000000) : ℝ) = ((50000000000 / 60543287093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5539_neg : (191822029 / 1000000000) ≤ -Real.log (500000000000 / 605727447031) ∧
    -Real.log (500000000000 / 605727447031) ≤ (19182203 / 100000000) := by
  have h := checkLog_sound (w := (105727447031 / 1105727447031)) (n := 12)
    (lo := (191822029 / 1000000000)) (hi := (19182203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605727447031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605727447031 / 500000000000) = 1/(500000000000 / 605727447031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5539 : Bounds (191822029 / 1000000000) (19182203 / 100000000) (Real.log (605727447031 / 500000000000)) := by
  have h := reflection_log_5539_neg
  have he : Real.log (605727447031 / 500000000000) = -Real.log (500000000000 / 605727447031) := by
    rw [show ((605727447031 / 500000000000) : ℝ) = ((500000000000 / 605727447031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5540_neg : (6000811 / 15625000) ≤ -Real.log (500000000000 / 734110823151) ∧
    -Real.log (500000000000 / 734110823151) ≤ (76810381 / 200000000) := by
  have h := checkLog_sound (w := (234110823151 / 1234110823151)) (n := 12)
    (lo := (6000811 / 15625000)) (hi := (76810381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734110823151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734110823151 / 500000000000) = 1/(500000000000 / 734110823151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5540 : Bounds (6000811 / 15625000) (76810381 / 200000000) (Real.log (734110823151 / 500000000000)) := by
  have h := reflection_log_5540_neg
  have he : Real.log (734110823151 / 500000000000) = -Real.log (500000000000 / 734110823151) := by
    rw [show ((734110823151 / 500000000000) : ℝ) = ((500000000000 / 734110823151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5541_neg : (384259373 / 1000000000) ≤ -Real.log (500000000000 / 734263144903) ∧
    -Real.log (500000000000 / 734263144903) ≤ (192129687 / 500000000) := by
  have h := checkLog_sound (w := (234263144903 / 1234263144903)) (n := 12)
    (lo := (384259373 / 1000000000)) (hi := (192129687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734263144903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734263144903 / 500000000000) = 1/(500000000000 / 734263144903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5541 : Bounds (384259373 / 1000000000) (192129687 / 500000000) (Real.log (734263144903 / 500000000000)) := by
  have h := reflection_log_5541_neg
  have he : Real.log (734263144903 / 500000000000) = -Real.log (500000000000 / 734263144903) := by
    rw [show ((734263144903 / 500000000000) : ℝ) = ((500000000000 / 734263144903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5542_neg : (173869269 / 1000000000) ≤ -Real.log (10000 / 11899) ∧
    -Real.log (10000 / 11899) ≤ (17386927 / 100000000) := by
  have h := checkLog_sound (w := (1899 / 21899)) (n := 12)
    (lo := (173869269 / 1000000000)) (hi := (17386927 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11899 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11899 / 10000) = 1/(10000 / 11899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5542 : Bounds (173869269 / 1000000000) (17386927 / 100000000) (Real.log (11899 / 10000)) := by
  have h := reflection_log_5542_neg
  have he : Real.log (11899 / 10000) = -Real.log (10000 / 11899) := by
    rw [show ((11899 / 10000) : ℝ) = ((10000 / 11899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5543_neg : (105298791 / 500000000) ≤ -Real.log (8101 / 10000) ∧
    -Real.log (8101 / 10000) ≤ (210597583 / 1000000000) := by
  have h := checkLog_sound (w := (1899 / 18101)) (n := 12)
    (lo := (105298791 / 500000000)) (hi := (210597583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8101) = 1/(8101 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5543 : Bounds (-210597583 / 1000000000) (-105298791 / 500000000) (Real.log (8101 / 10000)) := by
  have h := reflection_log_5543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5544_neg : (189881 / 1000000000) ≤ -Real.log (10000000 / 10001899) ∧
    -Real.log (10000000 / 10001899) ≤ (94941 / 500000000) := by
  have h := checkLog_sound (w := (1899 / 20001899)) (n := 12)
    (lo := (189881 / 1000000000)) (hi := (94941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001899 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001899 / 10000000) = 1/(10000000 / 10001899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5544 : Bounds (189881 / 1000000000) (94941 / 500000000) (Real.log (10001899 / 10000000)) := by
  have h := reflection_log_5544_neg
  have he : Real.log (10001899 / 10000000) = -Real.log (10000000 / 10001899) := by
    rw [show ((10001899 / 10000000) : ℝ) = ((10000000 / 10001899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5545_neg : (94959 / 500000000) ≤ -Real.log (9998101 / 10000000) ∧
    -Real.log (9998101 / 10000000) ≤ (189919 / 1000000000) := by
  have h := checkLog_sound (w := (1899 / 19998101)) (n := 12)
    (lo := (94959 / 500000000)) (hi := (189919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998101) = 1/(9998101 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5545 : Bounds (-189919 / 1000000000) (-94959 / 500000000) (Real.log (9998101 / 10000000)) := by
  have h := reflection_log_5545_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5546_neg : (45572577 / 500000000) ≤ -Real.log (250000 / 273857) ∧
    -Real.log (250000 / 273857) ≤ (18229031 / 200000000) := by
  have h := checkLog_sound (w := (23857 / 523857)) (n := 12)
    (lo := (45572577 / 500000000)) (hi := (18229031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273857 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273857 / 250000) = 1/(250000 / 273857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5546 : Bounds (45572577 / 500000000) (18229031 / 200000000) (Real.log (273857 / 250000)) := by
  have h := reflection_log_5546_neg
  have he : Real.log (273857 / 250000) = -Real.log (250000 / 273857) := by
    rw [show ((273857 / 250000) : ℝ) = ((250000 / 273857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5547_neg : (802347 / 8000000) ≤ -Real.log (226143 / 250000) ∧
    -Real.log (226143 / 250000) ≤ (391771 / 3906250) := by
  have h := checkLog_sound (w := (23857 / 476143)) (n := 12)
    (lo := (802347 / 8000000)) (hi := (391771 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226143) = 1/(226143 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5547 : Bounds (-391771 / 3906250) (-802347 / 8000000) (Real.log (226143 / 250000)) := by
  have h := reflection_log_5547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5548_neg : (18273027 / 200000000) ≤ -Real.log (1000000 / 1095669) ∧
    -Real.log (1000000 / 1095669) ≤ (5710321 / 62500000) := by
  have h := checkLog_sound (w := (95669 / 2095669)) (n := 12)
    (lo := (18273027 / 200000000)) (hi := (5710321 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095669 / 1000000) = 1/(1000000 / 1095669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5548 : Bounds (18273027 / 200000000) (5710321 / 62500000) (Real.log (1095669 / 1000000)) := by
  have h := reflection_log_5548_neg
  have he : Real.log (1095669 / 1000000) = -Real.log (1000000 / 1095669) := by
    rw [show ((1095669 / 1000000) : ℝ) = ((1000000 / 1095669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5549_neg : (20111967 / 200000000) ≤ -Real.log (904331 / 1000000) ∧
    -Real.log (904331 / 1000000) ≤ (25139959 / 250000000) := by
  have h := checkLog_sound (w := (95669 / 1904331)) (n := 12)
    (lo := (20111967 / 200000000)) (hi := (25139959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904331) = 1/(904331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5549 : Bounds (-25139959 / 250000000) (-20111967 / 200000000) (Real.log (904331 / 1000000)) := by
  have h := reflection_log_5549_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5550_neg : (9194699 / 1000000000) ≤ -Real.log (990847442439 / 1000000000000) ∧
    -Real.log (990847442439 / 1000000000000) ≤ (91947 / 10000000) := by
  have h := checkLog_sound (w := (9152557561 / 1990847442439)) (n := 12)
    (lo := (9194699 / 1000000000)) (hi := (91947 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990847442439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990847442439) = 1/(990847442439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5550 : Bounds (-91947 / 10000000) (-9194699 / 1000000000) (Real.log (990847442439 / 1000000000000)) := by
  have h := reflection_log_5550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5551_neg : (457411 / 50000000) ≤ -Real.log (61930843551 / 62500000000) ∧
    -Real.log (61930843551 / 62500000000) ≤ (9148221 / 1000000000) := by
  have h := checkLog_sound (w := (569156449 / 124430843551)) (n := 12)
    (lo := (457411 / 50000000)) (hi := (9148221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61930843551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61930843551) = 1/(61930843551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5551 : Bounds (-9148221 / 1000000000) (-457411 / 50000000) (Real.log (61930843551 / 62500000000)) := by
  have h := reflection_log_5551_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5552_neg : (191438529 / 1000000000) ≤ -Real.log (500000000000 / 605495195517) ∧
    -Real.log (500000000000 / 605495195517) ≤ (19143853 / 100000000) := by
  have h := checkLog_sound (w := (105495195517 / 1105495195517)) (n := 12)
    (lo := (191438529 / 1000000000)) (hi := (19143853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605495195517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605495195517 / 500000000000) = 1/(500000000000 / 605495195517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5552 : Bounds (191438529 / 1000000000) (19143853 / 100000000) (Real.log (605495195517 / 500000000000)) := by
  have h := reflection_log_5552_neg
  have he : Real.log (605495195517 / 500000000000) = -Real.log (500000000000 / 605495195517) := by
    rw [show ((605495195517 / 500000000000) : ℝ) = ((500000000000 / 605495195517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5553_neg : (19192497 / 100000000) ≤ -Real.log (12500000000 / 15144745121) ∧
    -Real.log (12500000000 / 15144745121) ≤ (191924971 / 1000000000) := by
  have h := checkLog_sound (w := (2644745121 / 27644745121)) (n := 12)
    (lo := (19192497 / 100000000)) (hi := (191924971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15144745121 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15144745121 / 12500000000) = 1/(12500000000 / 15144745121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5553 : Bounds (19192497 / 100000000) (191924971 / 1000000000) (Real.log (15144745121 / 12500000000)) := by
  have h := reflection_log_5553_neg
  have he : Real.log (15144745121 / 12500000000) = -Real.log (12500000000 / 15144745121) := by
    rw [show ((15144745121 / 12500000000) : ℝ) = ((12500000000 / 15144745121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5554_neg : (384259373 / 1000000000) ≤ -Real.log (250000000000 / 367131572451) ∧
    -Real.log (250000000000 / 367131572451) ≤ (192129687 / 500000000) := by
  have h := checkLog_sound (w := (117131572451 / 617131572451)) (n := 12)
    (lo := (384259373 / 1000000000)) (hi := (192129687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367131572451 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367131572451 / 250000000000) = 1/(250000000000 / 367131572451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5554 : Bounds (384259373 / 1000000000) (192129687 / 500000000) (Real.log (367131572451 / 250000000000)) := by
  have h := reflection_log_5554_neg
  have he : Real.log (367131572451 / 250000000000) = -Real.log (250000000000 / 367131572451) := by
    rw [show ((367131572451 / 250000000000) : ℝ) = ((250000000000 / 367131572451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5555_neg : (96116713 / 250000000) ≤ -Real.log (500000000000 / 734415504259) ∧
    -Real.log (500000000000 / 734415504259) ≤ (384466853 / 1000000000) := by
  have h := checkLog_sound (w := (234415504259 / 1234415504259)) (n := 12)
    (lo := (96116713 / 250000000)) (hi := (384466853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734415504259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734415504259 / 500000000000) = 1/(500000000000 / 734415504259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5555 : Bounds (96116713 / 250000000) (384466853 / 1000000000) (Real.log (734415504259 / 500000000000)) := by
  have h := reflection_log_5555_neg
  have he : Real.log (734415504259 / 500000000000) = -Real.log (500000000000 / 734415504259) := by
    rw [show ((734415504259 / 500000000000) : ℝ) = ((500000000000 / 734415504259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5556_neg : (173953307 / 1000000000) ≤ -Real.log (100 / 119) ∧
    -Real.log (100 / 119) ≤ (43488327 / 250000000) := by
  have h := checkLog_sound (w := (19 / 219)) (n := 12)
    (lo := (173953307 / 1000000000)) (hi := (43488327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119 / 100) = 1/(100 / 119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5556 : Bounds (173953307 / 1000000000) (43488327 / 250000000) (Real.log (119 / 100)) := by
  have h := reflection_log_5556_neg
  have he : Real.log (119 / 100) = -Real.log (100 / 119) := by
    rw [show ((119 / 100) : ℝ) = ((100 / 119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5557_neg : (210721031 / 1000000000) ≤ -Real.log (81 / 100) ∧
    -Real.log (81 / 100) ≤ (26340129 / 125000000) := by
  have h := checkLog_sound (w := (19 / 181)) (n := 12)
    (lo := (210721031 / 1000000000)) (hi := (26340129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 81) = 1/(81 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5557 : Bounds (-26340129 / 125000000) (-210721031 / 1000000000) (Real.log (81 / 100)) := by
  have h := reflection_log_5557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5558_neg : (189981 / 1000000000) ≤ -Real.log (100000 / 100019) ∧
    -Real.log (100000 / 100019) ≤ (94991 / 500000000) := by
  have h := checkLog_sound (w := (19 / 200019)) (n := 12)
    (lo := (189981 / 1000000000)) (hi := (94991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100019 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100019 / 100000) = 1/(100000 / 100019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5558 : Bounds (189981 / 1000000000) (94991 / 500000000) (Real.log (100019 / 100000)) := by
  have h := reflection_log_5558_neg
  have he : Real.log (100019 / 100000) = -Real.log (100000 / 100019) := by
    rw [show ((100019 / 100000) : ℝ) = ((100000 / 100019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5559_neg : (95009 / 500000000) ≤ -Real.log (99981 / 100000) ∧
    -Real.log (99981 / 100000) ≤ (190019 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 199981)) (n := 12)
    (lo := (95009 / 500000000)) (hi := (190019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99981) = 1/(99981 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5559 : Bounds (-190019 / 1000000000) (-95009 / 500000000) (Real.log (99981 / 100000)) := by
  have h := reflection_log_5559_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5560_neg : (9119171 / 100000000) ≤ -Real.log (1000000 / 1095479) ∧
    -Real.log (1000000 / 1095479) ≤ (91191711 / 1000000000) := by
  have h := checkLog_sound (w := (95479 / 2095479)) (n := 12)
    (lo := (9119171 / 100000000)) (hi := (91191711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095479 / 1000000) = 1/(1000000 / 1095479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5560 : Bounds (9119171 / 100000000) (91191711 / 1000000000) (Real.log (1095479 / 1000000)) := by
  have h := reflection_log_5560_neg
  have he : Real.log (1095479 / 1000000) = -Real.log (1000000 / 1095479) := by
    rw [show ((1095479 / 1000000) : ℝ) = ((1000000 / 1095479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5561_neg : (100349757 / 1000000000) ≤ -Real.log (904521 / 1000000) ∧
    -Real.log (904521 / 1000000) ≤ (50174879 / 500000000) := by
  have h := checkLog_sound (w := (95479 / 1904521)) (n := 12)
    (lo := (100349757 / 1000000000)) (hi := (50174879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904521) = 1/(904521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5561 : Bounds (-50174879 / 500000000) (-100349757 / 1000000000) (Real.log (904521 / 1000000)) := by
  have h := reflection_log_5561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5562_neg : (91411681 / 1000000000) ≤ -Real.log (25000 / 27393) ∧
    -Real.log (25000 / 27393) ≤ (45705841 / 500000000) := by
  have h := checkLog_sound (w := (2393 / 52393)) (n := 12)
    (lo := (91411681 / 1000000000)) (hi := (45705841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27393 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27393 / 25000) = 1/(25000 / 27393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5562 : Bounds (91411681 / 1000000000) (45705841 / 500000000) (Real.log (27393 / 25000)) := by
  have h := reflection_log_5562_neg
  have he : Real.log (27393 / 25000) = -Real.log (25000 / 27393) := by
    rw [show ((27393 / 25000) : ℝ) = ((25000 / 27393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5563_neg : (12577029 / 125000000) ≤ -Real.log (22607 / 25000) ∧
    -Real.log (22607 / 25000) ≤ (100616233 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 47607)) (n := 12)
    (lo := (12577029 / 125000000)) (hi := (100616233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22607) = 1/(22607 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5563 : Bounds (-100616233 / 1000000000) (-12577029 / 125000000) (Real.log (22607 / 25000)) := by
  have h := reflection_log_5563_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5564_neg : (184091 / 20000000) ≤ -Real.log (619273551 / 625000000) ∧
    -Real.log (619273551 / 625000000) ≤ (9204551 / 1000000000) := by
  have h := checkLog_sound (w := (5726449 / 1244273551)) (n := 12)
    (lo := (184091 / 20000000)) (hi := (9204551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 619273551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 619273551) = 1/(619273551 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5564 : Bounds (-9204551 / 1000000000) (-184091 / 20000000) (Real.log (619273551 / 625000000)) := by
  have h := reflection_log_5564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5565_neg : (4579023 / 500000000) ≤ -Real.log (990883760559 / 1000000000000) ∧
    -Real.log (990883760559 / 1000000000000) ≤ (9158047 / 1000000000) := by
  have h := checkLog_sound (w := (9116239441 / 1990883760559)) (n := 12)
    (lo := (4579023 / 500000000)) (hi := (9158047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990883760559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990883760559) = 1/(990883760559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5565 : Bounds (-9158047 / 1000000000) (-4579023 / 500000000) (Real.log (990883760559 / 1000000000000)) := by
  have h := reflection_log_5565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5566_neg : (191541467 / 1000000000) ≤ -Real.log (500000000000 / 605557527133) ∧
    -Real.log (500000000000 / 605557527133) ≤ (47885367 / 250000000) := by
  have h := checkLog_sound (w := (105557527133 / 1105557527133)) (n := 12)
    (lo := (191541467 / 1000000000)) (hi := (47885367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605557527133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605557527133 / 500000000000) = 1/(500000000000 / 605557527133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5566 : Bounds (191541467 / 1000000000) (47885367 / 250000000) (Real.log (605557527133 / 500000000000)) := by
  have h := reflection_log_5566_neg
  have he : Real.log (605557527133 / 500000000000) = -Real.log (500000000000 / 605557527133) := by
    rw [show ((605557527133 / 500000000000) : ℝ) = ((500000000000 / 605557527133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5567_neg : (192027913 / 1000000000) ≤ -Real.log (250000000000 / 302926084841) ∧
    -Real.log (250000000000 / 302926084841) ≤ (96013957 / 500000000) := by
  have h := checkLog_sound (w := (52926084841 / 552926084841)) (n := 12)
    (lo := (192027913 / 1000000000)) (hi := (96013957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302926084841 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302926084841 / 250000000000) = 1/(250000000000 / 302926084841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5567 : Bounds (192027913 / 1000000000) (96013957 / 500000000) (Real.log (302926084841 / 250000000000)) := by
  have h := reflection_log_5567_neg
  have he : Real.log (302926084841 / 250000000000) = -Real.log (250000000000 / 302926084841) := by
    rw [show ((302926084841 / 250000000000) : ℝ) = ((250000000000 / 302926084841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0087 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5568_neg : (96116713 / 250000000) ≤ -Real.log (250000000000 / 367207752129) ∧
    -Real.log (250000000000 / 367207752129) ≤ (384466853 / 1000000000) := by
  have h := checkLog_sound (w := (117207752129 / 617207752129)) (n := 12)
    (lo := (96116713 / 250000000)) (hi := (384466853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367207752129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367207752129 / 250000000000) = 1/(250000000000 / 367207752129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5568 : Bounds (96116713 / 250000000) (384466853 / 1000000000) (Real.log (367207752129 / 250000000000)) := by
  have h := reflection_log_5568_neg
  have he : Real.log (367207752129 / 250000000000) = -Real.log (250000000000 / 367207752129) := by
    rw [show ((367207752129 / 250000000000) : ℝ) = ((250000000000 / 367207752129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5569_neg : (192337169 / 500000000) ≤ -Real.log (100000000000 / 146913580247) ∧
    -Real.log (100000000000 / 146913580247) ≤ (384674339 / 1000000000) := by
  have h := checkLog_sound (w := (46913580247 / 246913580247)) (n := 12)
    (lo := (192337169 / 500000000)) (hi := (384674339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146913580247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146913580247 / 100000000000) = 1/(100000000000 / 146913580247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5569 : Bounds (192337169 / 500000000) (384674339 / 1000000000) (Real.log (146913580247 / 100000000000)) := by
  have h := reflection_log_5569_neg
  have he : Real.log (146913580247 / 100000000000) = -Real.log (100000000000 / 146913580247) := by
    rw [show ((146913580247 / 100000000000) : ℝ) = ((100000000000 / 146913580247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5570_neg : (174037337 / 1000000000) ≤ -Real.log (10000 / 11901) ∧
    -Real.log (10000 / 11901) ≤ (87018669 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 21901)) (n := 12)
    (lo := (174037337 / 1000000000)) (hi := (87018669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11901 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11901 / 10000) = 1/(10000 / 11901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5570 : Bounds (174037337 / 1000000000) (87018669 / 500000000) (Real.log (11901 / 10000)) := by
  have h := reflection_log_5570_neg
  have he : Real.log (11901 / 10000) = -Real.log (10000 / 11901) := by
    rw [show ((11901 / 10000) : ℝ) = ((10000 / 11901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5571_neg : (42168899 / 200000000) ≤ -Real.log (8099 / 10000) ∧
    -Real.log (8099 / 10000) ≤ (13177781 / 62500000) := by
  have h := checkLog_sound (w := (1901 / 18099)) (n := 12)
    (lo := (42168899 / 200000000)) (hi := (13177781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8099) = 1/(8099 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5571 : Bounds (-13177781 / 62500000) (-42168899 / 200000000) (Real.log (8099 / 10000)) := by
  have h := reflection_log_5571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5572_neg : (190081 / 1000000000) ≤ -Real.log (10000000 / 10001901) ∧
    -Real.log (10000000 / 10001901) ≤ (95041 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 20001901)) (n := 12)
    (lo := (190081 / 1000000000)) (hi := (95041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001901 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001901 / 10000000) = 1/(10000000 / 10001901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5572 : Bounds (190081 / 1000000000) (95041 / 500000000) (Real.log (10001901 / 10000000)) := by
  have h := reflection_log_5572_neg
  have he : Real.log (10001901 / 10000000) = -Real.log (10000000 / 10001901) := by
    rw [show ((10001901 / 10000000) : ℝ) = ((10000000 / 10001901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5573_neg : (95059 / 500000000) ≤ -Real.log (9998099 / 10000000) ∧
    -Real.log (9998099 / 10000000) ≤ (190119 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 19998099)) (n := 12)
    (lo := (95059 / 500000000)) (hi := (190119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998099) = 1/(9998099 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5573 : Bounds (-190119 / 1000000000) (-95059 / 500000000) (Real.log (9998099 / 10000000)) := by
  have h := reflection_log_5573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5574_neg : (11404783 / 125000000) ≤ -Real.log (100000 / 109553) ∧
    -Real.log (100000 / 109553) ≤ (18247653 / 200000000) := by
  have h := checkLog_sound (w := (9553 / 209553)) (n := 12)
    (lo := (11404783 / 125000000)) (hi := (18247653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109553 / 100000) = 1/(100000 / 109553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5574 : Bounds (11404783 / 125000000) (18247653 / 200000000) (Real.log (109553 / 100000)) := by
  have h := reflection_log_5574_neg
  have he : Real.log (109553 / 100000) = -Real.log (100000 / 109553) := by
    rw [show ((109553 / 100000) : ℝ) = ((100000 / 109553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5575_neg : (50203071 / 500000000) ≤ -Real.log (90447 / 100000) ∧
    -Real.log (90447 / 100000) ≤ (100406143 / 1000000000) := by
  have h := checkLog_sound (w := (9553 / 190447)) (n := 12)
    (lo := (50203071 / 500000000)) (hi := (100406143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90447) = 1/(90447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5575 : Bounds (-100406143 / 1000000000) (-50203071 / 500000000) (Real.log (90447 / 100000)) := by
  have h := reflection_log_5575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5576_neg : (3658329 / 40000000) ≤ -Real.log (1000000 / 1095771) ∧
    -Real.log (1000000 / 1095771) ≤ (45729113 / 500000000) := by
  have h := checkLog_sound (w := (95771 / 2095771)) (n := 12)
    (lo := (3658329 / 40000000)) (hi := (45729113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095771 / 1000000) = 1/(1000000 / 1095771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5576 : Bounds (3658329 / 40000000) (45729113 / 500000000) (Real.log (1095771 / 1000000)) := by
  have h := reflection_log_5576_neg
  have he : Real.log (1095771 / 1000000) = -Real.log (1000000 / 1095771) := by
    rw [show ((1095771 / 1000000) : ℝ) = ((1000000 / 1095771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5577_neg : (12584079 / 125000000) ≤ -Real.log (904229 / 1000000) ∧
    -Real.log (904229 / 1000000) ≤ (100672633 / 1000000000) := by
  have h := checkLog_sound (w := (95771 / 1904229)) (n := 12)
    (lo := (12584079 / 125000000)) (hi := (100672633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904229) = 1/(904229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5577 : Bounds (-100672633 / 1000000000) (-12584079 / 125000000) (Real.log (904229 / 1000000)) := by
  have h := reflection_log_5577_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5578_neg : (4607203 / 500000000) ≤ -Real.log (990827915559 / 1000000000000) ∧
    -Real.log (990827915559 / 1000000000000) ≤ (9214407 / 1000000000) := by
  have h := checkLog_sound (w := (9172084441 / 1990827915559)) (n := 12)
    (lo := (4607203 / 500000000)) (hi := (9214407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990827915559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990827915559) = 1/(990827915559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5578 : Bounds (-9214407 / 1000000000) (-4607203 / 500000000) (Real.log (990827915559 / 1000000000000)) := by
  have h := reflection_log_5578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5579_neg : (9167877 / 1000000000) ≤ -Real.log (9908740191 / 10000000000) ∧
    -Real.log (9908740191 / 10000000000) ≤ (4583939 / 500000000) := by
  have h := checkLog_sound (w := (91259809 / 19908740191)) (n := 12)
    (lo := (9167877 / 1000000000)) (hi := (4583939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9908740191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9908740191) = 1/(9908740191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5579 : Bounds (-4583939 / 500000000) (-9167877 / 1000000000) (Real.log (9908740191 / 10000000000)) := by
  have h := reflection_log_5579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5580_neg : (95822203 / 500000000) ≤ -Real.log (500000000000 / 605619865777) ∧
    -Real.log (500000000000 / 605619865777) ≤ (191644407 / 1000000000) := by
  have h := checkLog_sound (w := (105619865777 / 1105619865777)) (n := 12)
    (lo := (95822203 / 500000000)) (hi := (191644407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605619865777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605619865777 / 500000000000) = 1/(500000000000 / 605619865777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5580 : Bounds (95822203 / 500000000) (191644407 / 1000000000) (Real.log (605619865777 / 500000000000)) := by
  have h := reflection_log_5580_neg
  have he : Real.log (605619865777 / 500000000000) = -Real.log (500000000000 / 605619865777) := by
    rw [show ((605619865777 / 500000000000) : ℝ) = ((500000000000 / 605619865777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5581_neg : (192130857 / 1000000000) ≤ -Real.log (12500000000 / 15147863539) ∧
    -Real.log (12500000000 / 15147863539) ≤ (96065429 / 500000000) := by
  have h := checkLog_sound (w := (2647863539 / 27647863539)) (n := 12)
    (lo := (192130857 / 1000000000)) (hi := (96065429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15147863539 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15147863539 / 12500000000) = 1/(12500000000 / 15147863539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5581 : Bounds (192130857 / 1000000000) (96065429 / 500000000) (Real.log (15147863539 / 12500000000)) := by
  have h := reflection_log_5581_neg
  have he : Real.log (15147863539 / 12500000000) = -Real.log (12500000000 / 15147863539) := by
    rw [show ((15147863539 / 12500000000) : ℝ) = ((12500000000 / 15147863539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5582_neg : (192337169 / 500000000) ≤ -Real.log (250000000000 / 367283950617) ∧
    -Real.log (250000000000 / 367283950617) ≤ (384674339 / 1000000000) := by
  have h := checkLog_sound (w := (117283950617 / 617283950617)) (n := 12)
    (lo := (192337169 / 500000000)) (hi := (384674339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367283950617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367283950617 / 250000000000) = 1/(250000000000 / 367283950617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5582 : Bounds (192337169 / 500000000) (384674339 / 1000000000) (Real.log (367283950617 / 250000000000)) := by
  have h := reflection_log_5582_neg
  have he : Real.log (367283950617 / 250000000000) = -Real.log (250000000000 / 367283950617) := by
    rw [show ((367283950617 / 250000000000) : ℝ) = ((250000000000 / 367283950617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5583_neg : (48110229 / 125000000) ≤ -Real.log (125000000000 / 183680083961) ∧
    -Real.log (125000000000 / 183680083961) ≤ (384881833 / 1000000000) := by
  have h := checkLog_sound (w := (58680083961 / 308680083961)) (n := 12)
    (lo := (48110229 / 125000000)) (hi := (384881833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183680083961 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183680083961 / 125000000000) = 1/(125000000000 / 183680083961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5583 : Bounds (48110229 / 125000000) (384881833 / 1000000000) (Real.log (183680083961 / 125000000000)) := by
  have h := reflection_log_5583_neg
  have he : Real.log (183680083961 / 125000000000) = -Real.log (125000000000 / 183680083961) := by
    rw [show ((183680083961 / 125000000000) : ℝ) = ((125000000000 / 183680083961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5584_neg : (2176517 / 12500000) ≤ -Real.log (5000 / 5951) ∧
    -Real.log (5000 / 5951) ≤ (174121361 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 10951)) (n := 12)
    (lo := (2176517 / 12500000)) (hi := (174121361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5951 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5951 / 5000) = 1/(5000 / 5951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5584 : Bounds (2176517 / 12500000) (174121361 / 1000000000) (Real.log (5951 / 5000)) := by
  have h := reflection_log_5584_neg
  have he : Real.log (5951 / 5000) = -Real.log (5000 / 5951) := by
    rw [show ((5951 / 5000) : ℝ) = ((5000 / 5951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5585_neg : (8438719 / 40000000) ≤ -Real.log (4049 / 5000) ∧
    -Real.log (4049 / 5000) ≤ (26370997 / 125000000) := by
  have h := checkLog_sound (w := (951 / 9049)) (n := 12)
    (lo := (8438719 / 40000000)) (hi := (26370997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4049) = 1/(4049 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5585 : Bounds (-26370997 / 125000000) (-8438719 / 40000000) (Real.log (4049 / 5000)) := by
  have h := reflection_log_5585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5586_neg : (190181 / 1000000000) ≤ -Real.log (5000000 / 5000951) ∧
    -Real.log (5000000 / 5000951) ≤ (95091 / 500000000) := by
  have h := checkLog_sound (w := (951 / 10000951)) (n := 12)
    (lo := (190181 / 1000000000)) (hi := (95091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000951 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000951 / 5000000) = 1/(5000000 / 5000951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5586 : Bounds (190181 / 1000000000) (95091 / 500000000) (Real.log (5000951 / 5000000)) := by
  have h := reflection_log_5586_neg
  have he : Real.log (5000951 / 5000000) = -Real.log (5000000 / 5000951) := by
    rw [show ((5000951 / 5000000) : ℝ) = ((5000000 / 5000951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5587_neg : (95109 / 500000000) ≤ -Real.log (4999049 / 5000000) ∧
    -Real.log (4999049 / 5000000) ≤ (190219 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 9999049)) (n := 12)
    (lo := (95109 / 500000000)) (hi := (190219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999049) = 1/(4999049 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5587 : Bounds (-190219 / 1000000000) (-95109 / 500000000) (Real.log (4999049 / 5000000)) := by
  have h := reflection_log_5587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5588_neg : (5705301 / 62500000) ≤ -Real.log (1000000 / 1095581) ∧
    -Real.log (1000000 / 1095581) ≤ (91284817 / 1000000000) := by
  have h := checkLog_sound (w := (95581 / 2095581)) (n := 12)
    (lo := (5705301 / 62500000)) (hi := (91284817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095581 / 1000000) = 1/(1000000 / 1095581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5588 : Bounds (5705301 / 62500000) (91284817 / 1000000000) (Real.log (1095581 / 1000000)) := by
  have h := reflection_log_5588_neg
  have he : Real.log (1095581 / 1000000) = -Real.log (1000000 / 1095581) := by
    rw [show ((1095581 / 1000000) : ℝ) = ((1000000 / 1095581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5589_neg : (10046253 / 100000000) ≤ -Real.log (904419 / 1000000) ∧
    -Real.log (904419 / 1000000) ≤ (100462531 / 1000000000) := by
  have h := checkLog_sound (w := (95581 / 1904419)) (n := 12)
    (lo := (10046253 / 100000000)) (hi := (100462531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904419) = 1/(904419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5589 : Bounds (-100462531 / 1000000000) (-10046253 / 100000000) (Real.log (904419 / 1000000)) := by
  have h := reflection_log_5589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5590_neg : (45752383 / 500000000) ≤ -Real.log (500000 / 547911) ∧
    -Real.log (500000 / 547911) ≤ (91504767 / 1000000000) := by
  have h := checkLog_sound (w := (47911 / 1047911)) (n := 12)
    (lo := (45752383 / 500000000)) (hi := (91504767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547911 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547911 / 500000) = 1/(500000 / 547911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5590 : Bounds (45752383 / 500000000) (91504767 / 1000000000) (Real.log (547911 / 500000)) := by
  have h := reflection_log_5590_neg
  have he : Real.log (547911 / 500000) = -Real.log (500000 / 547911) := by
    rw [show ((547911 / 500000) : ℝ) = ((500000 / 547911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5591_neg : (20145807 / 200000000) ≤ -Real.log (452089 / 500000) ∧
    -Real.log (452089 / 500000) ≤ (25182259 / 250000000) := by
  have h := checkLog_sound (w := (47911 / 952089)) (n := 12)
    (lo := (20145807 / 200000000)) (hi := (25182259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452089) = 1/(452089 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5591 : Bounds (-25182259 / 250000000) (-20145807 / 200000000) (Real.log (452089 / 500000)) := by
  have h := reflection_log_5591_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5592_neg : (2306067 / 250000000) ≤ -Real.log (247704536079 / 250000000000) ∧
    -Real.log (247704536079 / 250000000000) ≤ (9224269 / 1000000000) := by
  have h := checkLog_sound (w := (2295463921 / 497704536079)) (n := 12)
    (lo := (2306067 / 250000000)) (hi := (9224269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247704536079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247704536079) = 1/(247704536079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5592 : Bounds (-9224269 / 1000000000) (-2306067 / 250000000) (Real.log (247704536079 / 250000000000)) := by
  have h := reflection_log_5592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5593_neg : (4588857 / 500000000) ≤ -Real.log (990864272439 / 1000000000000) ∧
    -Real.log (990864272439 / 1000000000000) ≤ (1835543 / 200000000) := by
  have h := checkLog_sound (w := (9135727561 / 1990864272439)) (n := 12)
    (lo := (4588857 / 500000000)) (hi := (1835543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990864272439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990864272439) = 1/(990864272439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5593 : Bounds (-1835543 / 200000000) (-4588857 / 500000000) (Real.log (990864272439 / 1000000000000)) := by
  have h := reflection_log_5593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5594_neg : (95873673 / 500000000) ≤ -Real.log (125000000000 / 151420552863) ∧
    -Real.log (125000000000 / 151420552863) ≤ (191747347 / 1000000000) := by
  have h := checkLog_sound (w := (26420552863 / 276420552863)) (n := 12)
    (lo := (95873673 / 500000000)) (hi := (191747347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151420552863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151420552863 / 125000000000) = 1/(125000000000 / 151420552863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5594 : Bounds (95873673 / 500000000) (191747347 / 1000000000) (Real.log (151420552863 / 125000000000)) := by
  have h := reflection_log_5594_neg
  have he : Real.log (151420552863 / 125000000000) = -Real.log (125000000000 / 151420552863) := by
    rw [show ((151420552863 / 125000000000) : ℝ) = ((125000000000 / 151420552863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5595_neg : (192233801 / 1000000000) ≤ -Real.log (250000000000 / 302988460237) ∧
    -Real.log (250000000000 / 302988460237) ≤ (96116901 / 500000000) := by
  have h := checkLog_sound (w := (52988460237 / 552988460237)) (n := 12)
    (lo := (192233801 / 1000000000)) (hi := (96116901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302988460237 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302988460237 / 250000000000) = 1/(250000000000 / 302988460237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5595 : Bounds (192233801 / 1000000000) (96116901 / 500000000) (Real.log (302988460237 / 250000000000)) := by
  have h := reflection_log_5595_neg
  have he : Real.log (302988460237 / 250000000000) = -Real.log (250000000000 / 302988460237) := by
    rw [show ((302988460237 / 250000000000) : ℝ) = ((250000000000 / 302988460237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5596_neg : (48110229 / 125000000) ≤ -Real.log (500000000000 / 734720335843) ∧
    -Real.log (500000000000 / 734720335843) ≤ (384881833 / 1000000000) := by
  have h := checkLog_sound (w := (234720335843 / 1234720335843)) (n := 12)
    (lo := (48110229 / 125000000)) (hi := (384881833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734720335843 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734720335843 / 500000000000) = 1/(500000000000 / 734720335843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5596 : Bounds (48110229 / 125000000) (384881833 / 1000000000) (Real.log (734720335843 / 500000000000)) := by
  have h := reflection_log_5596_neg
  have he : Real.log (734720335843 / 500000000000) = -Real.log (500000000000 / 734720335843) := by
    rw [show ((734720335843 / 500000000000) : ℝ) = ((500000000000 / 734720335843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5597_neg : (77017867 / 200000000) ≤ -Real.log (500000000000 / 734872808101) ∧
    -Real.log (500000000000 / 734872808101) ≤ (48136167 / 125000000) := by
  have h := checkLog_sound (w := (234872808101 / 1234872808101)) (n := 12)
    (lo := (77017867 / 200000000)) (hi := (48136167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734872808101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734872808101 / 500000000000) = 1/(500000000000 / 734872808101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5597 : Bounds (77017867 / 200000000) (48136167 / 125000000) (Real.log (734872808101 / 500000000000)) := by
  have h := reflection_log_5597_neg
  have he : Real.log (734872808101 / 500000000000) = -Real.log (500000000000 / 734872808101) := by
    rw [show ((734872808101 / 500000000000) : ℝ) = ((500000000000 / 734872808101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5598_neg : (2721959 / 15625000) ≤ -Real.log (10000 / 11903) ∧
    -Real.log (10000 / 11903) ≤ (174205377 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 21903)) (n := 12)
    (lo := (2721959 / 15625000)) (hi := (174205377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11903 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11903 / 10000) = 1/(10000 / 11903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5598 : Bounds (2721959 / 15625000) (174205377 / 1000000000) (Real.log (11903 / 10000)) := by
  have h := reflection_log_5598_neg
  have he : Real.log (11903 / 10000) = -Real.log (10000 / 11903) := by
    rw [show ((11903 / 10000) : ℝ) = ((10000 / 11903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5599_neg : (21109147 / 100000000) ≤ -Real.log (8097 / 10000) ∧
    -Real.log (8097 / 10000) ≤ (211091471 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 18097)) (n := 12)
    (lo := (21109147 / 100000000)) (hi := (211091471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8097) = 1/(8097 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5599 : Bounds (-211091471 / 1000000000) (-21109147 / 100000000) (Real.log (8097 / 10000)) := by
  have h := reflection_log_5599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5600_neg : (190281 / 1000000000) ≤ -Real.log (10000000 / 10001903) ∧
    -Real.log (10000000 / 10001903) ≤ (95141 / 500000000) := by
  have h := checkLog_sound (w := (1903 / 20001903)) (n := 12)
    (lo := (190281 / 1000000000)) (hi := (95141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001903 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001903 / 10000000) = 1/(10000000 / 10001903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5600 : Bounds (190281 / 1000000000) (95141 / 500000000) (Real.log (10001903 / 10000000)) := by
  have h := reflection_log_5600_neg
  have he : Real.log (10001903 / 10000000) = -Real.log (10000000 / 10001903) := by
    rw [show ((10001903 / 10000000) : ℝ) = ((10000000 / 10001903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5601_neg : (95159 / 500000000) ≤ -Real.log (9998097 / 10000000) ∧
    -Real.log (9998097 / 10000000) ≤ (190319 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 19998097)) (n := 12)
    (lo := (95159 / 500000000)) (hi := (190319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998097) = 1/(9998097 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5601 : Bounds (-190319 / 1000000000) (-95159 / 500000000) (Real.log (9998097 / 10000000)) := by
  have h := reflection_log_5601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5602_neg : (18266273 / 200000000) ≤ -Real.log (62500 / 68477) ∧
    -Real.log (62500 / 68477) ≤ (45665683 / 500000000) := by
  have h := checkLog_sound (w := (5977 / 130977)) (n := 12)
    (lo := (18266273 / 200000000)) (hi := (45665683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68477 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68477 / 62500) = 1/(62500 / 68477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5602 : Bounds (18266273 / 200000000) (45665683 / 500000000) (Real.log (68477 / 62500)) := by
  have h := reflection_log_5602_neg
  have he : Real.log (68477 / 62500) = -Real.log (62500 / 68477) := by
    rw [show ((68477 / 62500) : ℝ) = ((62500 / 68477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5603_neg : (100518921 / 1000000000) ≤ -Real.log (56523 / 62500) ∧
    -Real.log (56523 / 62500) ≤ (50259461 / 500000000) := by
  have h := checkLog_sound (w := (5977 / 119023)) (n := 12)
    (lo := (100518921 / 1000000000)) (hi := (50259461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56523) = 1/(56523 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5603 : Bounds (-50259461 / 500000000) (-100518921 / 1000000000) (Real.log (56523 / 62500)) := by
  have h := reflection_log_5603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5604_neg : (18310261 / 200000000) ≤ -Real.log (1000000 / 1095873) ∧
    -Real.log (1000000 / 1095873) ≤ (45775653 / 500000000) := by
  have h := checkLog_sound (w := (95873 / 2095873)) (n := 12)
    (lo := (18310261 / 200000000)) (hi := (45775653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095873 / 1000000) = 1/(1000000 / 1095873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5604 : Bounds (18310261 / 200000000) (45775653 / 500000000) (Real.log (1095873 / 1000000)) := by
  have h := reflection_log_5604_neg
  have he : Real.log (1095873 / 1000000) = -Real.log (1000000 / 1095873) := by
    rw [show ((1095873 / 1000000) : ℝ) = ((1000000 / 1095873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5605_neg : (100785441 / 1000000000) ≤ -Real.log (904127 / 1000000) ∧
    -Real.log (904127 / 1000000) ≤ (50392721 / 500000000) := by
  have h := checkLog_sound (w := (95873 / 1904127)) (n := 12)
    (lo := (100785441 / 1000000000)) (hi := (50392721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904127) = 1/(904127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5605 : Bounds (-50392721 / 500000000) (-100785441 / 1000000000) (Real.log (904127 / 1000000)) := by
  have h := reflection_log_5605_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5606_neg : (1846827 / 200000000) ≤ -Real.log (990808367871 / 1000000000000) ∧
    -Real.log (990808367871 / 1000000000000) ≤ (1154267 / 125000000) := by
  have h := checkLog_sound (w := (9191632129 / 1990808367871)) (n := 12)
    (lo := (1846827 / 200000000)) (hi := (1154267 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990808367871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990808367871) = 1/(990808367871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5606 : Bounds (-1154267 / 125000000) (-1846827 / 200000000) (Real.log (990808367871 / 1000000000000)) := by
  have h := reflection_log_5606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5607_neg : (2296889 / 250000000) ≤ -Real.log (3870525471 / 3906250000) ∧
    -Real.log (3870525471 / 3906250000) ≤ (9187557 / 1000000000) := by
  have h := checkLog_sound (w := (35724529 / 7776775471)) (n := 12)
    (lo := (2296889 / 250000000)) (hi := (9187557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3870525471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3870525471) = 1/(3870525471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5607 : Bounds (-9187557 / 1000000000) (-2296889 / 250000000) (Real.log (3870525471 / 3906250000)) := by
  have h := reflection_log_5607_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5608_neg : (191850287 / 1000000000) ≤ -Real.log (500000000000 / 605744564159) ∧
    -Real.log (500000000000 / 605744564159) ≤ (11990643 / 62500000) := by
  have h := checkLog_sound (w := (105744564159 / 1105744564159)) (n := 12)
    (lo := (191850287 / 1000000000)) (hi := (11990643 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605744564159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605744564159 / 500000000000) = 1/(500000000000 / 605744564159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5608 : Bounds (191850287 / 1000000000) (11990643 / 62500000) (Real.log (605744564159 / 500000000000)) := by
  have h := reflection_log_5608_neg
  have he : Real.log (605744564159 / 500000000000) = -Real.log (500000000000 / 605744564159) := by
    rw [show ((605744564159 / 500000000000) : ℝ) = ((500000000000 / 605744564159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5609_neg : (192336747 / 1000000000) ≤ -Real.log (20000000000 / 24241572257) ∧
    -Real.log (20000000000 / 24241572257) ≤ (48084187 / 250000000) := by
  have h := checkLog_sound (w := (4241572257 / 44241572257)) (n := 12)
    (lo := (192336747 / 1000000000)) (hi := (48084187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24241572257 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24241572257 / 20000000000) = 1/(20000000000 / 24241572257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5609 : Bounds (192336747 / 1000000000) (48084187 / 250000000) (Real.log (24241572257 / 20000000000)) := by
  have h := reflection_log_5609_neg
  have he : Real.log (24241572257 / 20000000000) = -Real.log (20000000000 / 24241572257) := by
    rw [show ((24241572257 / 20000000000) : ℝ) = ((20000000000 / 24241572257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5610_neg : (77017867 / 200000000) ≤ -Real.log (5000000000 / 7348728081) ∧
    -Real.log (5000000000 / 7348728081) ≤ (48136167 / 125000000) := by
  have h := checkLog_sound (w := (2348728081 / 12348728081)) (n := 12)
    (lo := (77017867 / 200000000)) (hi := (48136167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7348728081 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7348728081 / 5000000000) = 1/(5000000000 / 7348728081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5610 : Bounds (77017867 / 200000000) (48136167 / 125000000) (Real.log (7348728081 / 5000000000)) := by
  have h := reflection_log_5610_neg
  have he : Real.log (7348728081 / 5000000000) = -Real.log (5000000000 / 7348728081) := by
    rw [show ((7348728081 / 5000000000) : ℝ) = ((5000000000 / 7348728081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5611_neg : (192648423 / 500000000) ≤ -Real.log (25000000000 / 36751265901) ∧
    -Real.log (25000000000 / 36751265901) ≤ (385296847 / 1000000000) := by
  have h := checkLog_sound (w := (11751265901 / 61751265901)) (n := 12)
    (lo := (192648423 / 500000000)) (hi := (385296847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36751265901 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36751265901 / 25000000000) = 1/(25000000000 / 36751265901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5611 : Bounds (192648423 / 500000000) (385296847 / 1000000000) (Real.log (36751265901 / 25000000000)) := by
  have h := reflection_log_5611_neg
  have he : Real.log (36751265901 / 25000000000) = -Real.log (25000000000 / 36751265901) := by
    rw [show ((36751265901 / 25000000000) : ℝ) = ((25000000000 / 36751265901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5612_neg : (34857877 / 200000000) ≤ -Real.log (625 / 744) ∧
    -Real.log (625 / 744) ≤ (87144693 / 500000000) := by
  have h := checkLog_sound (w := (119 / 1369)) (n := 12)
    (lo := (34857877 / 200000000)) (hi := (87144693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744 / 625) = 1/(625 / 744) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5612 : Bounds (34857877 / 200000000) (87144693 / 500000000) (Real.log (744 / 625)) := by
  have h := reflection_log_5612_neg
  have he : Real.log (744 / 625) = -Real.log (625 / 744) := by
    rw [show ((744 / 625) : ℝ) = ((625 / 744) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5613_neg : (10560749 / 50000000) ≤ -Real.log (506 / 625) ∧
    -Real.log (506 / 625) ≤ (211214981 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 1131)) (n := 12)
    (lo := (10560749 / 50000000)) (hi := (211214981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 506) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 506) = 1/(506 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5613 : Bounds (-211214981 / 1000000000) (-10560749 / 50000000) (Real.log (506 / 625)) := by
  have h := reflection_log_5613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5614_neg : (190381 / 1000000000) ≤ -Real.log (625000 / 625119) ∧
    -Real.log (625000 / 625119) ≤ (95191 / 500000000) := by
  have h := checkLog_sound (w := (119 / 1250119)) (n := 12)
    (lo := (190381 / 1000000000)) (hi := (95191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625119 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625119 / 625000) = 1/(625000 / 625119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5614 : Bounds (190381 / 1000000000) (95191 / 500000000) (Real.log (625119 / 625000)) := by
  have h := reflection_log_5614_neg
  have he : Real.log (625119 / 625000) = -Real.log (625000 / 625119) := by
    rw [show ((625119 / 625000) : ℝ) = ((625000 / 625119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5615_neg : (95209 / 500000000) ≤ -Real.log (624881 / 625000) ∧
    -Real.log (624881 / 625000) ≤ (190419 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 1249881)) (n := 12)
    (lo := (95209 / 500000000)) (hi := (190419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624881) = 1/(624881 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5615 : Bounds (-190419 / 1000000000) (-95209 / 500000000) (Real.log (624881 / 625000)) := by
  have h := reflection_log_5615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5616_neg : (91377913 / 1000000000) ≤ -Real.log (1000000 / 1095683) ∧
    -Real.log (1000000 / 1095683) ≤ (45688957 / 500000000) := by
  have h := checkLog_sound (w := (95683 / 2095683)) (n := 12)
    (lo := (91377913 / 1000000000)) (hi := (45688957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095683 / 1000000) = 1/(1000000 / 1095683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5616 : Bounds (91377913 / 1000000000) (45688957 / 500000000) (Real.log (1095683 / 1000000)) := by
  have h := reflection_log_5616_neg
  have he : Real.log (1095683 / 1000000) = -Real.log (1000000 / 1095683) := by
    rw [show ((1095683 / 1000000) : ℝ) = ((1000000 / 1095683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5617_neg : (25143829 / 250000000) ≤ -Real.log (904317 / 1000000) ∧
    -Real.log (904317 / 1000000) ≤ (100575317 / 1000000000) := by
  have h := checkLog_sound (w := (95683 / 1904317)) (n := 12)
    (lo := (25143829 / 250000000)) (hi := (100575317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904317) = 1/(904317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5617 : Bounds (-100575317 / 1000000000) (-25143829 / 250000000) (Real.log (904317 / 1000000)) := by
  have h := reflection_log_5617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5618_neg : (91597843 / 1000000000) ≤ -Real.log (250000 / 273981) ∧
    -Real.log (250000 / 273981) ≤ (22899461 / 250000000) := by
  have h := checkLog_sound (w := (23981 / 523981)) (n := 12)
    (lo := (91597843 / 1000000000)) (hi := (22899461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273981 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273981 / 250000) = 1/(250000 / 273981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5618 : Bounds (91597843 / 1000000000) (22899461 / 250000000) (Real.log (273981 / 250000)) := by
  have h := reflection_log_5618_neg
  have he : Real.log (273981 / 250000) = -Real.log (250000 / 273981) := by
    rw [show ((273981 / 250000) : ℝ) = ((250000 / 273981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5619_neg : (100841851 / 1000000000) ≤ -Real.log (226019 / 250000) ∧
    -Real.log (226019 / 250000) ≤ (25210463 / 250000000) := by
  have h := checkLog_sound (w := (23981 / 476019)) (n := 12)
    (lo := (100841851 / 1000000000)) (hi := (25210463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226019) = 1/(226019 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5619 : Bounds (-25210463 / 250000000) (-100841851 / 1000000000) (Real.log (226019 / 250000)) := by
  have h := reflection_log_5619_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5620_neg : (1155501 / 125000000) ≤ -Real.log (61924911639 / 62500000000) ∧
    -Real.log (61924911639 / 62500000000) ≤ (9244009 / 1000000000) := by
  have h := checkLog_sound (w := (575088361 / 124424911639)) (n := 12)
    (lo := (1155501 / 125000000)) (hi := (9244009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61924911639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61924911639) = 1/(61924911639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5620 : Bounds (-9244009 / 1000000000) (-1155501 / 125000000) (Real.log (61924911639 / 62500000000)) := by
  have h := reflection_log_5620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5621_neg : (9197403 / 1000000000) ≤ -Real.log (990844763511 / 1000000000000) ∧
    -Real.log (990844763511 / 1000000000000) ≤ (2299351 / 250000000) := by
  have h := checkLog_sound (w := (9155236489 / 1990844763511)) (n := 12)
    (lo := (9197403 / 1000000000)) (hi := (2299351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990844763511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990844763511) = 1/(990844763511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5621 : Bounds (-2299351 / 250000000) (-9197403 / 1000000000) (Real.log (990844763511 / 1000000000000)) := by
  have h := reflection_log_5621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5622_neg : (191953229 / 1000000000) ≤ -Real.log (500000000000 / 605806923899) ∧
    -Real.log (500000000000 / 605806923899) ≤ (19195323 / 100000000) := by
  have h := checkLog_sound (w := (105806923899 / 1105806923899)) (n := 12)
    (lo := (191953229 / 1000000000)) (hi := (19195323 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605806923899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605806923899 / 500000000000) = 1/(500000000000 / 605806923899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5622 : Bounds (191953229 / 1000000000) (19195323 / 100000000) (Real.log (605806923899 / 500000000000)) := by
  have h := reflection_log_5622_neg
  have he : Real.log (605806923899 / 500000000000) = -Real.log (500000000000 / 605806923899) := by
    rw [show ((605806923899 / 500000000000) : ℝ) = ((500000000000 / 605806923899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5623_neg : (96219847 / 500000000) ≤ -Real.log (100000000000 / 121220339883) ∧
    -Real.log (100000000000 / 121220339883) ≤ (38487939 / 200000000) := by
  have h := checkLog_sound (w := (21220339883 / 221220339883)) (n := 12)
    (lo := (96219847 / 500000000)) (hi := (38487939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121220339883 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121220339883 / 100000000000) = 1/(100000000000 / 121220339883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5623 : Bounds (96219847 / 500000000) (38487939 / 200000000) (Real.log (121220339883 / 100000000000)) := by
  have h := reflection_log_5623_neg
  have he : Real.log (121220339883 / 100000000000) = -Real.log (100000000000 / 121220339883) := by
    rw [show ((121220339883 / 100000000000) : ℝ) = ((100000000000 / 121220339883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5624_neg : (192648423 / 500000000) ≤ -Real.log (500000000000 / 735025318019) ∧
    -Real.log (500000000000 / 735025318019) ≤ (385296847 / 1000000000) := by
  have h := checkLog_sound (w := (235025318019 / 1235025318019)) (n := 12)
    (lo := (192648423 / 500000000)) (hi := (385296847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735025318019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735025318019 / 500000000000) = 1/(500000000000 / 735025318019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5624 : Bounds (192648423 / 500000000) (385296847 / 1000000000) (Real.log (735025318019 / 500000000000)) := by
  have h := reflection_log_5624_neg
  have he : Real.log (735025318019 / 500000000000) = -Real.log (500000000000 / 735025318019) := by
    rw [show ((735025318019 / 500000000000) : ℝ) = ((500000000000 / 735025318019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5625_neg : (77100873 / 200000000) ≤ -Real.log (500000000000 / 735177865613) ∧
    -Real.log (500000000000 / 735177865613) ≤ (192752183 / 500000000) := by
  have h := checkLog_sound (w := (235177865613 / 1235177865613)) (n := 12)
    (lo := (77100873 / 200000000)) (hi := (192752183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735177865613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735177865613 / 500000000000) = 1/(500000000000 / 735177865613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5625 : Bounds (77100873 / 200000000) (192752183 / 500000000) (Real.log (735177865613 / 500000000000)) := by
  have h := reflection_log_5625_neg
  have he : Real.log (735177865613 / 500000000000) = -Real.log (500000000000 / 735177865613) := by
    rw [show ((735177865613 / 500000000000) : ℝ) = ((500000000000 / 735177865613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5626_neg : (87186693 / 500000000) ≤ -Real.log (2000 / 2381) ∧
    -Real.log (2000 / 2381) ≤ (174373387 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 4381)) (n := 12)
    (lo := (87186693 / 500000000)) (hi := (174373387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2381 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2381 / 2000) = 1/(2000 / 2381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5626 : Bounds (87186693 / 500000000) (174373387 / 1000000000) (Real.log (2381 / 2000)) := by
  have h := reflection_log_5626_neg
  have he : Real.log (2381 / 2000) = -Real.log (2000 / 2381) := by
    rw [show ((2381 / 2000) : ℝ) = ((2000 / 2381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5627_neg : (42267701 / 200000000) ≤ -Real.log (1619 / 2000) ∧
    -Real.log (1619 / 2000) ≤ (105669253 / 500000000) := by
  have h := checkLog_sound (w := (381 / 3619)) (n := 12)
    (lo := (42267701 / 200000000)) (hi := (105669253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1619) = 1/(1619 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5627 : Bounds (-105669253 / 500000000) (-42267701 / 200000000) (Real.log (1619 / 2000)) := by
  have h := reflection_log_5627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5628_neg : (190481 / 1000000000) ≤ -Real.log (2000000 / 2000381) ∧
    -Real.log (2000000 / 2000381) ≤ (95241 / 500000000) := by
  have h := checkLog_sound (w := (381 / 4000381)) (n := 12)
    (lo := (190481 / 1000000000)) (hi := (95241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000381 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000381 / 2000000) = 1/(2000000 / 2000381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5628 : Bounds (190481 / 1000000000) (95241 / 500000000) (Real.log (2000381 / 2000000)) := by
  have h := reflection_log_5628_neg
  have he : Real.log (2000381 / 2000000) = -Real.log (2000000 / 2000381) := by
    rw [show ((2000381 / 2000000) : ℝ) = ((2000000 / 2000381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5629_neg : (95259 / 500000000) ≤ -Real.log (1999619 / 2000000) ∧
    -Real.log (1999619 / 2000000) ≤ (190519 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 3999619)) (n := 12)
    (lo := (95259 / 500000000)) (hi := (190519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999619) = 1/(1999619 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5629 : Bounds (-190519 / 1000000000) (-95259 / 500000000) (Real.log (1999619 / 2000000)) := by
  have h := reflection_log_5629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5630_neg : (45712229 / 500000000) ≤ -Real.log (500000 / 547867) ∧
    -Real.log (500000 / 547867) ≤ (91424459 / 1000000000) := by
  have h := checkLog_sound (w := (47867 / 1047867)) (n := 12)
    (lo := (45712229 / 500000000)) (hi := (91424459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547867 / 500000) = 1/(500000 / 547867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5630 : Bounds (45712229 / 500000000) (91424459 / 1000000000) (Real.log (547867 / 500000)) := by
  have h := reflection_log_5630_neg
  have he : Real.log (547867 / 500000) = -Real.log (500000 / 547867) := by
    rw [show ((547867 / 500000) : ℝ) = ((500000 / 547867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5631_neg : (50315857 / 500000000) ≤ -Real.log (452133 / 500000) ∧
    -Real.log (452133 / 500000) ≤ (20126343 / 200000000) := by
  have h := checkLog_sound (w := (47867 / 952133)) (n := 12)
    (lo := (50315857 / 500000000)) (hi := (20126343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452133) = 1/(452133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5631 : Bounds (-20126343 / 200000000) (-50315857 / 500000000) (Real.log (452133 / 500000)) := by
  have h := reflection_log_5631_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


