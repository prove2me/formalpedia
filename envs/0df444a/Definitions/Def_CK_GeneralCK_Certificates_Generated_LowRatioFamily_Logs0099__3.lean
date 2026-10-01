-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0099__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0099__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:14:57.016964+00:00
-- url     : https://prove2.me/theorems/19e2aafc-acaa-4891-ab09-4c47931bd596
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0099 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0100, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0099 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0100, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0101)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0099 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0100, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0101)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0099 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0100, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0101) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0099 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0100, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0101).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0099 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6336_neg : (98601303 / 500000000) ≤ -Real.log (250000000000 / 304497697171) ∧
    -Real.log (250000000000 / 304497697171) ≤ (197202607 / 1000000000) := by
  have h := checkLog_sound (w := (54497697171 / 554497697171)) (n := 12)
    (lo := (98601303 / 500000000)) (hi := (197202607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304497697171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304497697171 / 250000000000) = 1/(250000000000 / 304497697171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6336 : Bounds (98601303 / 500000000) (197202607 / 1000000000) (Real.log (304497697171 / 250000000000)) := by
  have h := reflection_log_6336_neg
  have he : Real.log (304497697171 / 250000000000) = -Real.log (250000000000 / 304497697171) := by
    rw [show ((304497697171 / 250000000000) : ℝ) = ((250000000000 / 304497697171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6337_neg : (197699417 / 1000000000) ≤ -Real.log (500000000000 / 609298025117) ∧
    -Real.log (500000000000 / 609298025117) ≤ (98849709 / 500000000) := by
  have h := checkLog_sound (w := (109298025117 / 1109298025117)) (n := 12)
    (lo := (197699417 / 1000000000)) (hi := (98849709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609298025117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609298025117 / 500000000000) = 1/(500000000000 / 609298025117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6337 : Bounds (197699417 / 1000000000) (98849709 / 500000000) (Real.log (609298025117 / 500000000000)) := by
  have h := reflection_log_6337_neg
  have he : Real.log (609298025117 / 500000000000) = -Real.log (500000000000 / 609298025117) := by
    rw [show ((609298025117 / 500000000000) : ℝ) = ((500000000000 / 609298025117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6338_neg : (98972719 / 250000000) ≤ -Real.log (250000000000 / 371426795923) ∧
    -Real.log (250000000000 / 371426795923) ≤ (395890877 / 1000000000) := by
  have h := checkLog_sound (w := (121426795923 / 621426795923)) (n := 12)
    (lo := (98972719 / 250000000)) (hi := (395890877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371426795923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371426795923 / 250000000000) = 1/(250000000000 / 371426795923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6338 : Bounds (98972719 / 250000000) (395890877 / 1000000000) (Real.log (371426795923 / 250000000000)) := by
  have h := reflection_log_6338_neg
  have he : Real.log (371426795923 / 250000000000) = -Real.log (250000000000 / 371426795923) := by
    rw [show ((371426795923 / 250000000000) : ℝ) = ((250000000000 / 371426795923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6339_neg : (19804941 / 50000000) ≤ -Real.log (500000000000 / 743008079553) ∧
    -Real.log (500000000000 / 743008079553) ≤ (396098821 / 1000000000) := by
  have h := checkLog_sound (w := (243008079553 / 1243008079553)) (n := 12)
    (lo := (19804941 / 50000000)) (hi := (396098821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743008079553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743008079553 / 500000000000) = 1/(500000000000 / 743008079553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6339 : Bounds (19804941 / 50000000) (396098821 / 1000000000) (Real.log (743008079553 / 500000000000)) := by
  have h := reflection_log_6339_neg
  have he : Real.log (743008079553 / 500000000000) = -Real.log (500000000000 / 743008079553) := by
    rw [show ((743008079553 / 500000000000) : ℝ) = ((500000000000 / 743008079553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6340_neg : (178648151 / 1000000000) ≤ -Real.log (2500 / 2989) ∧
    -Real.log (2500 / 2989) ≤ (22331019 / 125000000) := by
  have h := checkLog_sound (w := (489 / 5489)) (n := 12)
    (lo := (178648151 / 1000000000)) (hi := (22331019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2989 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2989 / 2500) = 1/(2500 / 2989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6340 : Bounds (178648151 / 1000000000) (22331019 / 125000000) (Real.log (2989 / 2500)) := by
  have h := reflection_log_6340_neg
  have he : Real.log (2989 / 2500) = -Real.log (2500 / 2989) := by
    rw [show ((2989 / 2500) : ℝ) = ((2500 / 2989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6341_neg : (217658621 / 1000000000) ≤ -Real.log (2011 / 2500) ∧
    -Real.log (2011 / 2500) ≤ (108829311 / 500000000) := by
  have h := checkLog_sound (w := (489 / 4511)) (n := 12)
    (lo := (217658621 / 1000000000)) (hi := (108829311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2011) = 1/(2011 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6341 : Bounds (-108829311 / 500000000) (-217658621 / 1000000000) (Real.log (2011 / 2500)) := by
  have h := reflection_log_6341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6342_neg : (9779 / 50000000) ≤ -Real.log (2500000 / 2500489) ∧
    -Real.log (2500000 / 2500489) ≤ (195581 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 5000489)) (n := 12)
    (lo := (9779 / 50000000)) (hi := (195581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500489 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500489 / 2500000) = 1/(2500000 / 2500489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6342 : Bounds (9779 / 50000000) (195581 / 1000000000) (Real.log (2500489 / 2500000)) := by
  have h := reflection_log_6342_neg
  have he : Real.log (2500489 / 2500000) = -Real.log (2500000 / 2500489) := by
    rw [show ((2500489 / 2500000) : ℝ) = ((2500000 / 2500489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6343_neg : (195619 / 1000000000) ≤ -Real.log (2499511 / 2500000) ∧
    -Real.log (2499511 / 2500000) ≤ (9781 / 50000000) := by
  have h := checkLog_sound (w := (489 / 4999511)) (n := 12)
    (lo := (195619 / 1000000000)) (hi := (9781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499511) = 1/(2499511 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6343 : Bounds (-9781 / 50000000) (-195619 / 1000000000) (Real.log (2499511 / 2500000)) := by
  have h := reflection_log_6343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6344_neg : (46897243 / 500000000) ≤ -Real.log (500000 / 549167) ∧
    -Real.log (500000 / 549167) ≤ (93794487 / 1000000000) := by
  have h := checkLog_sound (w := (49167 / 1049167)) (n := 12)
    (lo := (46897243 / 500000000)) (hi := (93794487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549167 / 500000) = 1/(500000 / 549167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6344 : Bounds (46897243 / 500000000) (93794487 / 1000000000) (Real.log (549167 / 500000)) := by
  have h := reflection_log_6344_neg
  have he : Real.log (549167 / 500000) = -Real.log (500000 / 549167) := by
    rw [show ((549167 / 500000) : ℝ) = ((500000 / 549167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6345_neg : (20702223 / 200000000) ≤ -Real.log (450833 / 500000) ∧
    -Real.log (450833 / 500000) ≤ (25877779 / 250000000) := by
  have h := checkLog_sound (w := (49167 / 950833)) (n := 12)
    (lo := (20702223 / 200000000)) (hi := (25877779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450833) = 1/(450833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6345 : Bounds (-25877779 / 250000000) (-20702223 / 200000000) (Real.log (450833 / 500000)) := by
  have h := reflection_log_6345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6346_neg : (23504609 / 250000000) ≤ -Real.log (50000 / 54929) ∧
    -Real.log (50000 / 54929) ≤ (94018437 / 1000000000) := by
  have h := checkLog_sound (w := (4929 / 104929)) (n := 12)
    (lo := (23504609 / 250000000)) (hi := (94018437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54929 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54929 / 50000) = 1/(50000 / 54929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6346 : Bounds (23504609 / 250000000) (94018437 / 1000000000) (Real.log (54929 / 50000)) := by
  have h := reflection_log_6346_neg
  have he : Real.log (54929 / 50000) = -Real.log (50000 / 54929) := by
    rw [show ((54929 / 50000) : ℝ) = ((50000 / 54929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6347_neg : (103783981 / 1000000000) ≤ -Real.log (45071 / 50000) ∧
    -Real.log (45071 / 50000) ≤ (51891991 / 500000000) := by
  have h := checkLog_sound (w := (4929 / 95071)) (n := 12)
    (lo := (103783981 / 1000000000)) (hi := (51891991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45071) = 1/(45071 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6347 : Bounds (-51891991 / 500000000) (-103783981 / 1000000000) (Real.log (45071 / 50000)) := by
  have h := reflection_log_6347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6348_neg : (1220693 / 125000000) ≤ -Real.log (2475704959 / 2500000000) ∧
    -Real.log (2475704959 / 2500000000) ≤ (1953109 / 200000000) := by
  have h := checkLog_sound (w := (24295041 / 4975704959)) (n := 12)
    (lo := (1220693 / 125000000)) (hi := (1953109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2475704959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2475704959) = 1/(2475704959 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6348 : Bounds (-1953109 / 200000000) (-1220693 / 125000000) (Real.log (2475704959 / 2500000000)) := by
  have h := reflection_log_6348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6349_neg : (9716629 / 1000000000) ≤ -Real.log (247582606111 / 250000000000) ∧
    -Real.log (247582606111 / 250000000000) ≤ (971663 / 100000000) := by
  have h := checkLog_sound (w := (2417393889 / 497582606111)) (n := 12)
    (lo := (9716629 / 1000000000)) (hi := (971663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247582606111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247582606111) = 1/(247582606111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6349 : Bounds (-971663 / 100000000) (-9716629 / 1000000000) (Real.log (247582606111 / 250000000000)) := by
  have h := reflection_log_6349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6350_neg : (98652801 / 500000000) ≤ -Real.log (500000000000 / 609058121299) ∧
    -Real.log (500000000000 / 609058121299) ≤ (197305603 / 1000000000) := by
  have h := checkLog_sound (w := (109058121299 / 1109058121299)) (n := 12)
    (lo := (98652801 / 500000000)) (hi := (197305603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609058121299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609058121299 / 500000000000) = 1/(500000000000 / 609058121299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6350 : Bounds (98652801 / 500000000) (197305603 / 1000000000) (Real.log (609058121299 / 500000000000)) := by
  have h := reflection_log_6350_neg
  have he : Real.log (609058121299 / 500000000000) = -Real.log (500000000000 / 609058121299) := by
    rw [show ((609058121299 / 500000000000) : ℝ) = ((500000000000 / 609058121299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6351_neg : (98901209 / 500000000) ≤ -Real.log (100000000000 / 121872157263) ∧
    -Real.log (100000000000 / 121872157263) ≤ (197802419 / 1000000000) := by
  have h := checkLog_sound (w := (21872157263 / 221872157263)) (n := 12)
    (lo := (98901209 / 500000000)) (hi := (197802419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121872157263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121872157263 / 100000000000) = 1/(100000000000 / 121872157263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6351 : Bounds (98901209 / 500000000) (197802419 / 1000000000) (Real.log (121872157263 / 100000000000)) := by
  have h := reflection_log_6351_neg
  have he : Real.log (121872157263 / 100000000000) = -Real.log (100000000000 / 121872157263) := by
    rw [show ((121872157263 / 100000000000) : ℝ) = ((100000000000 / 121872157263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6352_neg : (19804941 / 50000000) ≤ -Real.log (7812500000 / 11609501243) ∧
    -Real.log (7812500000 / 11609501243) ≤ (396098821 / 1000000000) := by
  have h := checkLog_sound (w := (3797001243 / 19422001243)) (n := 12)
    (lo := (19804941 / 50000000)) (hi := (396098821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11609501243 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11609501243 / 7812500000) = 1/(7812500000 / 11609501243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6352 : Bounds (19804941 / 50000000) (396098821 / 1000000000) (Real.log (11609501243 / 7812500000)) := by
  have h := reflection_log_6352_neg
  have he : Real.log (11609501243 / 7812500000) = -Real.log (7812500000 / 11609501243) := by
    rw [show ((11609501243 / 7812500000) : ℝ) = ((7812500000 / 11609501243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6353_neg : (99076693 / 250000000) ≤ -Real.log (500000000000 / 743162605669) ∧
    -Real.log (500000000000 / 743162605669) ≤ (396306773 / 1000000000) := by
  have h := checkLog_sound (w := (243162605669 / 1243162605669)) (n := 12)
    (lo := (99076693 / 250000000)) (hi := (396306773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743162605669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743162605669 / 500000000000) = 1/(500000000000 / 743162605669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6353 : Bounds (99076693 / 250000000) (396306773 / 1000000000) (Real.log (743162605669 / 500000000000)) := by
  have h := reflection_log_6353_neg
  have he : Real.log (743162605669 / 500000000000) = -Real.log (500000000000 / 743162605669) := by
    rw [show ((743162605669 / 500000000000) : ℝ) = ((500000000000 / 743162605669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6354_neg : (178731787 / 1000000000) ≤ -Real.log (10000 / 11957) ∧
    -Real.log (10000 / 11957) ≤ (44682947 / 250000000) := by
  have h := checkLog_sound (w := (1957 / 21957)) (n := 12)
    (lo := (178731787 / 1000000000)) (hi := (44682947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11957 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11957 / 10000) = 1/(10000 / 11957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6354 : Bounds (178731787 / 1000000000) (44682947 / 250000000) (Real.log (11957 / 10000)) := by
  have h := reflection_log_6354_neg
  have he : Real.log (11957 / 10000) = -Real.log (10000 / 11957) := by
    rw [show ((11957 / 10000) : ℝ) = ((10000 / 11957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6355_neg : (43556589 / 200000000) ≤ -Real.log (8043 / 10000) ∧
    -Real.log (8043 / 10000) ≤ (108891473 / 500000000) := by
  have h := checkLog_sound (w := (1957 / 18043)) (n := 12)
    (lo := (43556589 / 200000000)) (hi := (108891473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8043) = 1/(8043 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6355 : Bounds (-108891473 / 500000000) (-43556589 / 200000000) (Real.log (8043 / 10000)) := by
  have h := reflection_log_6355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6356_neg : (1223 / 6250000) ≤ -Real.log (10000000 / 10001957) ∧
    -Real.log (10000000 / 10001957) ≤ (195681 / 1000000000) := by
  have h := checkLog_sound (w := (1957 / 20001957)) (n := 12)
    (lo := (1223 / 6250000)) (hi := (195681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001957 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001957 / 10000000) = 1/(10000000 / 10001957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6356 : Bounds (1223 / 6250000) (195681 / 1000000000) (Real.log (10001957 / 10000000)) := by
  have h := reflection_log_6356_neg
  have he : Real.log (10001957 / 10000000) = -Real.log (10000000 / 10001957) := by
    rw [show ((10001957 / 10000000) : ℝ) = ((10000000 / 10001957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6357_neg : (195719 / 1000000000) ≤ -Real.log (9998043 / 10000000) ∧
    -Real.log (9998043 / 10000000) ≤ (4893 / 25000000) := by
  have h := checkLog_sound (w := (1957 / 19998043)) (n := 12)
    (lo := (195719 / 1000000000)) (hi := (4893 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998043) = 1/(9998043 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6357 : Bounds (-4893 / 25000000) (-195719 / 1000000000) (Real.log (9998043 / 10000000)) := by
  have h := reflection_log_6357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6358_neg : (93840919 / 1000000000) ≤ -Real.log (200000 / 219677) ∧
    -Real.log (200000 / 219677) ≤ (2346023 / 25000000) := by
  have h := checkLog_sound (w := (19677 / 419677)) (n := 12)
    (lo := (93840919 / 1000000000)) (hi := (2346023 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219677 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219677 / 200000) = 1/(200000 / 219677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6358 : Bounds (93840919 / 1000000000) (2346023 / 25000000) (Real.log (219677 / 200000)) := by
  have h := reflection_log_6358_neg
  have he : Real.log (219677 / 200000) = -Real.log (200000 / 219677) := by
    rw [show ((219677 / 200000) : ℝ) = ((200000 / 219677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6359_neg : (103567679 / 1000000000) ≤ -Real.log (180323 / 200000) ∧
    -Real.log (180323 / 200000) ≤ (323649 / 3125000) := by
  have h := checkLog_sound (w := (19677 / 380323)) (n := 12)
    (lo := (103567679 / 1000000000)) (hi := (323649 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180323) = 1/(180323 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6359 : Bounds (-323649 / 3125000) (-103567679 / 1000000000) (Real.log (180323 / 200000)) := by
  have h := reflection_log_6359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6360_neg : (94064859 / 1000000000) ≤ -Real.log (1000000 / 1098631) ∧
    -Real.log (1000000 / 1098631) ≤ (4703243 / 50000000) := by
  have h := checkLog_sound (w := (98631 / 2098631)) (n := 12)
    (lo := (94064859 / 1000000000)) (hi := (4703243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098631 / 1000000) = 1/(1000000 / 1098631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6360 : Bounds (94064859 / 1000000000) (4703243 / 50000000) (Real.log (1098631 / 1000000)) := by
  have h := reflection_log_6360_neg
  have he : Real.log (1098631 / 1000000) = -Real.log (1000000 / 1098631) := by
    rw [show ((1098631 / 1000000) : ℝ) = ((1000000 / 1098631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6361_neg : (1298007 / 12500000) ≤ -Real.log (901369 / 1000000) ∧
    -Real.log (901369 / 1000000) ≤ (103840561 / 1000000000) := by
  have h := checkLog_sound (w := (98631 / 1901369)) (n := 12)
    (lo := (1298007 / 12500000)) (hi := (103840561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901369) = 1/(901369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6361 : Bounds (-103840561 / 1000000000) (-1298007 / 12500000) (Real.log (901369 / 1000000)) := by
  have h := reflection_log_6361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6362_neg : (9775701 / 1000000000) ≤ -Real.log (990271925839 / 1000000000000) ∧
    -Real.log (990271925839 / 1000000000000) ≤ (4887851 / 500000000) := by
  have h := checkLog_sound (w := (9728074161 / 1990271925839)) (n := 12)
    (lo := (9775701 / 1000000000)) (hi := (4887851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990271925839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990271925839) = 1/(990271925839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6362 : Bounds (-4887851 / 500000000) (-9775701 / 1000000000) (Real.log (990271925839 / 1000000000000)) := by
  have h := reflection_log_6362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6363_neg : (243169 / 25000000) ≤ -Real.log (39612815671 / 40000000000) ∧
    -Real.log (39612815671 / 40000000000) ≤ (9726761 / 1000000000) := by
  have h := checkLog_sound (w := (387184329 / 79612815671)) (n := 12)
    (lo := (243169 / 25000000)) (hi := (9726761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39612815671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39612815671) = 1/(39612815671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6363 : Bounds (-9726761 / 1000000000) (-243169 / 25000000) (Real.log (39612815671 / 40000000000)) := by
  have h := reflection_log_6363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6364_neg : (98704299 / 500000000) ≤ -Real.log (250000000000 / 304560427677) ∧
    -Real.log (250000000000 / 304560427677) ≤ (197408599 / 1000000000) := by
  have h := checkLog_sound (w := (54560427677 / 554560427677)) (n := 12)
    (lo := (98704299 / 500000000)) (hi := (197408599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304560427677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304560427677 / 250000000000) = 1/(250000000000 / 304560427677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6364 : Bounds (98704299 / 500000000) (197408599 / 1000000000) (Real.log (304560427677 / 250000000000)) := by
  have h := reflection_log_6364_neg
  have he : Real.log (304560427677 / 250000000000) = -Real.log (250000000000 / 304560427677) := by
    rw [show ((304560427677 / 250000000000) : ℝ) = ((250000000000 / 304560427677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6365_neg : (197905419 / 1000000000) ≤ -Real.log (62500000000 / 76177944327) ∧
    -Real.log (62500000000 / 76177944327) ≤ (9895271 / 50000000) := by
  have h := checkLog_sound (w := (13677944327 / 138677944327)) (n := 12)
    (lo := (197905419 / 1000000000)) (hi := (9895271 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76177944327 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76177944327 / 62500000000) = 1/(62500000000 / 76177944327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6365 : Bounds (197905419 / 1000000000) (9895271 / 50000000) (Real.log (76177944327 / 62500000000)) := by
  have h := reflection_log_6365_neg
  have he : Real.log (76177944327 / 62500000000) = -Real.log (62500000000 / 76177944327) := by
    rw [show ((76177944327 / 62500000000) : ℝ) = ((62500000000 / 76177944327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6366_neg : (99076693 / 250000000) ≤ -Real.log (125000000000 / 185790651417) ∧
    -Real.log (125000000000 / 185790651417) ≤ (396306773 / 1000000000) := by
  have h := checkLog_sound (w := (60790651417 / 310790651417)) (n := 12)
    (lo := (99076693 / 250000000)) (hi := (396306773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185790651417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185790651417 / 125000000000) = 1/(125000000000 / 185790651417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6366 : Bounds (99076693 / 250000000) (396306773 / 1000000000) (Real.log (185790651417 / 125000000000)) := by
  have h := reflection_log_6366_neg
  have he : Real.log (185790651417 / 125000000000) = -Real.log (125000000000 / 185790651417) := by
    rw [show ((185790651417 / 125000000000) : ℝ) = ((125000000000 / 185790651417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6367_neg : (396514733 / 1000000000) ≤ -Real.log (500000000000 / 743317170211) ∧
    -Real.log (500000000000 / 743317170211) ≤ (198257367 / 500000000) := by
  have h := checkLog_sound (w := (243317170211 / 1243317170211)) (n := 12)
    (lo := (396514733 / 1000000000)) (hi := (198257367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743317170211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743317170211 / 500000000000) = 1/(500000000000 / 743317170211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6367 : Bounds (396514733 / 1000000000) (198257367 / 500000000) (Real.log (743317170211 / 500000000000)) := by
  have h := reflection_log_6367_neg
  have he : Real.log (743317170211 / 500000000000) = -Real.log (500000000000 / 743317170211) := by
    rw [show ((743317170211 / 500000000000) : ℝ) = ((500000000000 / 743317170211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6368_neg : (178815417 / 1000000000) ≤ -Real.log (5000 / 5979) ∧
    -Real.log (5000 / 5979) ≤ (89407709 / 500000000) := by
  have h := checkLog_sound (w := (979 / 10979)) (n := 12)
    (lo := (178815417 / 1000000000)) (hi := (89407709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5979 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5979 / 5000) = 1/(5000 / 5979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6368 : Bounds (178815417 / 1000000000) (89407709 / 500000000) (Real.log (5979 / 5000)) := by
  have h := reflection_log_6368_neg
  have he : Real.log (5979 / 5000) = -Real.log (5000 / 5979) := by
    rw [show ((5979 / 5000) : ℝ) = ((5000 / 5979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6369_neg : (54476821 / 250000000) ≤ -Real.log (4021 / 5000) ∧
    -Real.log (4021 / 5000) ≤ (43581457 / 200000000) := by
  have h := checkLog_sound (w := (979 / 9021)) (n := 12)
    (lo := (54476821 / 250000000)) (hi := (43581457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4021) = 1/(4021 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6369 : Bounds (-43581457 / 200000000) (-54476821 / 250000000) (Real.log (4021 / 5000)) := by
  have h := reflection_log_6369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6370_neg : (9789 / 50000000) ≤ -Real.log (5000000 / 5000979) ∧
    -Real.log (5000000 / 5000979) ≤ (195781 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 10000979)) (n := 12)
    (lo := (9789 / 50000000)) (hi := (195781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000979 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000979 / 5000000) = 1/(5000000 / 5000979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6370 : Bounds (9789 / 50000000) (195781 / 1000000000) (Real.log (5000979 / 5000000)) := by
  have h := reflection_log_6370_neg
  have he : Real.log (5000979 / 5000000) = -Real.log (5000000 / 5000979) := by
    rw [show ((5000979 / 5000000) : ℝ) = ((5000000 / 5000979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6371_neg : (195819 / 1000000000) ≤ -Real.log (4999021 / 5000000) ∧
    -Real.log (4999021 / 5000000) ≤ (9791 / 50000000) := by
  have h := checkLog_sound (w := (979 / 9999021)) (n := 12)
    (lo := (195819 / 1000000000)) (hi := (9791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999021) = 1/(4999021 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6371 : Bounds (-9791 / 50000000) (-195819 / 1000000000) (Real.log (4999021 / 5000000)) := by
  have h := reflection_log_6371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6372_neg : (93887349 / 1000000000) ≤ -Real.log (250000 / 274609) ∧
    -Real.log (250000 / 274609) ≤ (1877747 / 20000000) := by
  have h := checkLog_sound (w := (24609 / 524609)) (n := 12)
    (lo := (93887349 / 1000000000)) (hi := (1877747 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274609 / 250000) = 1/(250000 / 274609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6372 : Bounds (93887349 / 1000000000) (1877747 / 20000000) (Real.log (274609 / 250000)) := by
  have h := reflection_log_6372_neg
  have he : Real.log (274609 / 250000) = -Real.log (250000 / 274609) := by
    rw [show ((274609 / 250000) : ℝ) = ((250000 / 274609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6373_neg : (51812123 / 500000000) ≤ -Real.log (225391 / 250000) ∧
    -Real.log (225391 / 250000) ≤ (103624247 / 1000000000) := by
  have h := checkLog_sound (w := (24609 / 475391)) (n := 12)
    (lo := (51812123 / 500000000)) (hi := (103624247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225391) = 1/(225391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6373 : Bounds (-103624247 / 1000000000) (-51812123 / 500000000) (Real.log (225391 / 250000)) := by
  have h := reflection_log_6373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6374_neg : (94111279 / 1000000000) ≤ -Real.log (500000 / 549341) ∧
    -Real.log (500000 / 549341) ≤ (1176391 / 12500000) := by
  have h := checkLog_sound (w := (49341 / 1049341)) (n := 12)
    (lo := (94111279 / 1000000000)) (hi := (1176391 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549341 / 500000) = 1/(500000 / 549341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6374 : Bounds (94111279 / 1000000000) (1176391 / 12500000) (Real.log (549341 / 500000)) := by
  have h := reflection_log_6374_neg
  have he : Real.log (549341 / 500000) = -Real.log (500000 / 549341) := by
    rw [show ((549341 / 500000) : ℝ) = ((500000 / 549341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6375_neg : (51948571 / 500000000) ≤ -Real.log (450659 / 500000) ∧
    -Real.log (450659 / 500000) ≤ (103897143 / 1000000000) := by
  have h := checkLog_sound (w := (49341 / 950659)) (n := 12)
    (lo := (51948571 / 500000000)) (hi := (103897143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450659) = 1/(450659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6375 : Bounds (-103897143 / 1000000000) (-51948571 / 500000000) (Real.log (450659 / 500000)) := by
  have h := reflection_log_6375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6376_neg : (4892931 / 500000000) ≤ -Real.log (247565465719 / 250000000000) ∧
    -Real.log (247565465719 / 250000000000) ≤ (9785863 / 1000000000) := by
  have h := checkLog_sound (w := (2434534281 / 497565465719)) (n := 12)
    (lo := (4892931 / 500000000)) (hi := (9785863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247565465719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247565465719) = 1/(247565465719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6376 : Bounds (-9785863 / 1000000000) (-4892931 / 500000000) (Real.log (247565465719 / 250000000000)) := by
  have h := reflection_log_6376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6377_neg : (152139 / 15625000) ≤ -Real.log (61894397119 / 62500000000) ∧
    -Real.log (61894397119 / 62500000000) ≤ (9736897 / 1000000000) := by
  have h := checkLog_sound (w := (605602881 / 124394397119)) (n := 12)
    (lo := (152139 / 15625000)) (hi := (9736897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61894397119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61894397119) = 1/(61894397119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6377 : Bounds (-9736897 / 1000000000) (-152139 / 15625000) (Real.log (61894397119 / 62500000000)) := by
  have h := reflection_log_6377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6378_neg : (39502319 / 200000000) ≤ -Real.log (100000000000 / 121836719301) ∧
    -Real.log (100000000000 / 121836719301) ≤ (49377899 / 250000000) := by
  have h := checkLog_sound (w := (21836719301 / 221836719301)) (n := 12)
    (lo := (39502319 / 200000000)) (hi := (49377899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121836719301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121836719301 / 100000000000) = 1/(100000000000 / 121836719301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6378 : Bounds (39502319 / 200000000) (49377899 / 250000000) (Real.log (121836719301 / 100000000000)) := by
  have h := reflection_log_6378_neg
  have he : Real.log (121836719301 / 100000000000) = -Real.log (100000000000 / 121836719301) := by
    rw [show ((121836719301 / 100000000000) : ℝ) = ((100000000000 / 121836719301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6379_neg : (99004211 / 500000000) ≤ -Real.log (500000000000 / 609486330019) ∧
    -Real.log (500000000000 / 609486330019) ≤ (198008423 / 1000000000) := by
  have h := checkLog_sound (w := (109486330019 / 1109486330019)) (n := 12)
    (lo := (99004211 / 500000000)) (hi := (198008423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609486330019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609486330019 / 500000000000) = 1/(500000000000 / 609486330019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6379 : Bounds (99004211 / 500000000) (198008423 / 1000000000) (Real.log (609486330019 / 500000000000)) := by
  have h := reflection_log_6379_neg
  have he : Real.log (609486330019 / 500000000000) = -Real.log (500000000000 / 609486330019) := by
    rw [show ((609486330019 / 500000000000) : ℝ) = ((500000000000 / 609486330019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6380_neg : (396514733 / 1000000000) ≤ -Real.log (50000000000 / 74331717021) ∧
    -Real.log (50000000000 / 74331717021) ≤ (198257367 / 500000000) := by
  have h := checkLog_sound (w := (24331717021 / 124331717021)) (n := 12)
    (lo := (396514733 / 1000000000)) (hi := (198257367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74331717021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74331717021 / 50000000000) = 1/(50000000000 / 74331717021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6380 : Bounds (396514733 / 1000000000) (198257367 / 500000000) (Real.log (74331717021 / 50000000000)) := by
  have h := reflection_log_6380_neg
  have he : Real.log (74331717021 / 50000000000) = -Real.log (50000000000 / 74331717021) := by
    rw [show ((74331717021 / 50000000000) : ℝ) = ((50000000000 / 74331717021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6381_neg : (396722701 / 1000000000) ≤ -Real.log (500000000000 / 743471773191) ∧
    -Real.log (500000000000 / 743471773191) ≤ (198361351 / 500000000) := by
  have h := checkLog_sound (w := (243471773191 / 1243471773191)) (n := 12)
    (lo := (396722701 / 1000000000)) (hi := (198361351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743471773191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743471773191 / 500000000000) = 1/(500000000000 / 743471773191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6381 : Bounds (396722701 / 1000000000) (198361351 / 500000000) (Real.log (743471773191 / 500000000000)) := by
  have h := reflection_log_6381_neg
  have he : Real.log (743471773191 / 500000000000) = -Real.log (500000000000 / 743471773191) := by
    rw [show ((743471773191 / 500000000000) : ℝ) = ((500000000000 / 743471773191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6382_neg : (178899039 / 1000000000) ≤ -Real.log (10000 / 11959) ∧
    -Real.log (10000 / 11959) ≤ (1118119 / 6250000) := by
  have h := checkLog_sound (w := (1959 / 21959)) (n := 12)
    (lo := (178899039 / 1000000000)) (hi := (1118119 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11959 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11959 / 10000) = 1/(10000 / 11959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6382 : Bounds (178899039 / 1000000000) (1118119 / 6250000) (Real.log (11959 / 10000)) := by
  have h := reflection_log_6382_neg
  have he : Real.log (11959 / 10000) = -Real.log (10000 / 11959) := by
    rw [show ((11959 / 10000) : ℝ) = ((10000 / 11959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6383_neg : (218031639 / 1000000000) ≤ -Real.log (8041 / 10000) ∧
    -Real.log (8041 / 10000) ≤ (5450791 / 25000000) := by
  have h := checkLog_sound (w := (1959 / 18041)) (n := 12)
    (lo := (218031639 / 1000000000)) (hi := (5450791 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8041) = 1/(8041 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6383 : Bounds (-5450791 / 25000000) (-218031639 / 1000000000) (Real.log (8041 / 10000)) := by
  have h := reflection_log_6383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6384_neg : (4897 / 25000000) ≤ -Real.log (10000000 / 10001959) ∧
    -Real.log (10000000 / 10001959) ≤ (195881 / 1000000000) := by
  have h := checkLog_sound (w := (1959 / 20001959)) (n := 12)
    (lo := (4897 / 25000000)) (hi := (195881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001959 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001959 / 10000000) = 1/(10000000 / 10001959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6384 : Bounds (4897 / 25000000) (195881 / 1000000000) (Real.log (10001959 / 10000000)) := by
  have h := reflection_log_6384_neg
  have he : Real.log (10001959 / 10000000) = -Real.log (10000000 / 10001959) := by
    rw [show ((10001959 / 10000000) : ℝ) = ((10000000 / 10001959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6385_neg : (195919 / 1000000000) ≤ -Real.log (9998041 / 10000000) ∧
    -Real.log (9998041 / 10000000) ≤ (2449 / 12500000) := by
  have h := checkLog_sound (w := (1959 / 19998041)) (n := 12)
    (lo := (195919 / 1000000000)) (hi := (2449 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998041) = 1/(9998041 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6385 : Bounds (-2449 / 12500000) (-195919 / 1000000000) (Real.log (9998041 / 10000000)) := by
  have h := reflection_log_6385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6386_neg : (46966889 / 500000000) ≤ -Real.log (1000000 / 1098487) ∧
    -Real.log (1000000 / 1098487) ≤ (93933779 / 1000000000) := by
  have h := checkLog_sound (w := (98487 / 2098487)) (n := 12)
    (lo := (46966889 / 500000000)) (hi := (93933779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098487 / 1000000) = 1/(1000000 / 1098487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6386 : Bounds (46966889 / 500000000) (93933779 / 1000000000) (Real.log (1098487 / 1000000)) := by
  have h := reflection_log_6386_neg
  have he : Real.log (1098487 / 1000000) = -Real.log (1000000 / 1098487) := by
    rw [show ((1098487 / 1000000) : ℝ) = ((1000000 / 1098487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6387_neg : (6480051 / 62500000) ≤ -Real.log (901513 / 1000000) ∧
    -Real.log (901513 / 1000000) ≤ (103680817 / 1000000000) := by
  have h := checkLog_sound (w := (98487 / 1901513)) (n := 12)
    (lo := (6480051 / 62500000)) (hi := (103680817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901513) = 1/(901513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6387 : Bounds (-103680817 / 1000000000) (-6480051 / 62500000) (Real.log (901513 / 1000000)) := by
  have h := reflection_log_6387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6388_neg : (94157697 / 1000000000) ≤ -Real.log (1000000 / 1098733) ∧
    -Real.log (1000000 / 1098733) ≤ (47078849 / 500000000) := by
  have h := checkLog_sound (w := (98733 / 2098733)) (n := 12)
    (lo := (94157697 / 1000000000)) (hi := (47078849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098733 / 1000000) = 1/(1000000 / 1098733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6388 : Bounds (94157697 / 1000000000) (47078849 / 500000000) (Real.log (1098733 / 1000000)) := by
  have h := reflection_log_6388_neg
  have he : Real.log (1098733 / 1000000) = -Real.log (1000000 / 1098733) := by
    rw [show ((1098733 / 1000000) : ℝ) = ((1000000 / 1098733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6389_neg : (103953727 / 1000000000) ≤ -Real.log (901267 / 1000000) ∧
    -Real.log (901267 / 1000000) ≤ (1624277 / 15625000) := by
  have h := checkLog_sound (w := (98733 / 1901267)) (n := 12)
    (lo := (103953727 / 1000000000)) (hi := (1624277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901267) = 1/(901267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6389 : Bounds (-1624277 / 15625000) (-103953727 / 1000000000) (Real.log (901267 / 1000000)) := by
  have h := reflection_log_6389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6390_neg : (979603 / 100000000) ≤ -Real.log (990251794711 / 1000000000000) ∧
    -Real.log (990251794711 / 1000000000000) ≤ (9796031 / 1000000000) := by
  have h := checkLog_sound (w := (9748205289 / 1990251794711)) (n := 12)
    (lo := (979603 / 100000000)) (hi := (9796031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990251794711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990251794711) = 1/(990251794711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6390 : Bounds (-9796031 / 1000000000) (-979603 / 100000000) (Real.log (990251794711 / 1000000000000)) := by
  have h := reflection_log_6390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6391_neg : (9747037 / 1000000000) ≤ -Real.log (990300310831 / 1000000000000) ∧
    -Real.log (990300310831 / 1000000000000) ≤ (4873519 / 500000000) := by
  have h := checkLog_sound (w := (9699689169 / 1990300310831)) (n := 12)
    (lo := (9747037 / 1000000000)) (hi := (4873519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990300310831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990300310831) = 1/(990300310831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6391 : Bounds (-4873519 / 500000000) (-9747037 / 1000000000) (Real.log (990300310831 / 1000000000000)) := by
  have h := reflection_log_6391_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6392_neg : (98807297 / 500000000) ≤ -Real.log (100000000000 / 121849268951) ∧
    -Real.log (100000000000 / 121849268951) ≤ (39522919 / 200000000) := by
  have h := checkLog_sound (w := (21849268951 / 221849268951)) (n := 12)
    (lo := (98807297 / 500000000)) (hi := (39522919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121849268951 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121849268951 / 100000000000) = 1/(100000000000 / 121849268951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6392 : Bounds (98807297 / 500000000) (39522919 / 200000000) (Real.log (121849268951 / 100000000000)) := by
  have h := reflection_log_6392_neg
  have he : Real.log (121849268951 / 100000000000) = -Real.log (100000000000 / 121849268951) := by
    rw [show ((121849268951 / 100000000000) : ℝ) = ((100000000000 / 121849268951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6393_neg : (7924457 / 40000000) ≤ -Real.log (31250000000 / 38096819533) ∧
    -Real.log (31250000000 / 38096819533) ≤ (99055713 / 500000000) := by
  have h := checkLog_sound (w := (6846819533 / 69346819533)) (n := 12)
    (lo := (7924457 / 40000000)) (hi := (99055713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38096819533 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38096819533 / 31250000000) = 1/(31250000000 / 38096819533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6393 : Bounds (7924457 / 40000000) (99055713 / 500000000) (Real.log (38096819533 / 31250000000)) := by
  have h := reflection_log_6393_neg
  have he : Real.log (38096819533 / 31250000000) = -Real.log (31250000000 / 38096819533) := by
    rw [show ((38096819533 / 31250000000) : ℝ) = ((31250000000 / 38096819533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6394_neg : (396722701 / 1000000000) ≤ -Real.log (50000000000 / 74347177319) ∧
    -Real.log (50000000000 / 74347177319) ≤ (198361351 / 500000000) := by
  have h := checkLog_sound (w := (24347177319 / 124347177319)) (n := 12)
    (lo := (396722701 / 1000000000)) (hi := (198361351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74347177319 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74347177319 / 50000000000) = 1/(50000000000 / 74347177319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6394 : Bounds (396722701 / 1000000000) (198361351 / 500000000) (Real.log (74347177319 / 50000000000)) := by
  have h := reflection_log_6394_neg
  have he : Real.log (74347177319 / 50000000000) = -Real.log (50000000000 / 74347177319) := by
    rw [show ((74347177319 / 50000000000) : ℝ) = ((50000000000 / 74347177319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6395_neg : (396930679 / 1000000000) ≤ -Real.log (250000000000 / 371813207313) ∧
    -Real.log (250000000000 / 371813207313) ≤ (9923267 / 25000000) := by
  have h := checkLog_sound (w := (121813207313 / 621813207313)) (n := 12)
    (lo := (396930679 / 1000000000)) (hi := (9923267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371813207313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371813207313 / 250000000000) = 1/(250000000000 / 371813207313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6395 : Bounds (396930679 / 1000000000) (9923267 / 25000000) (Real.log (371813207313 / 250000000000)) := by
  have h := reflection_log_6395_neg
  have he : Real.log (371813207313 / 250000000000) = -Real.log (250000000000 / 371813207313) := by
    rw [show ((371813207313 / 250000000000) : ℝ) = ((250000000000 / 371813207313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6396_neg : (35796531 / 200000000) ≤ -Real.log (250 / 299) ∧
    -Real.log (250 / 299) ≤ (699151 / 3906250) := by
  have h := checkLog_sound (w := (49 / 549)) (n := 12)
    (lo := (35796531 / 200000000)) (hi := (699151 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 250) = 1/(250 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6396 : Bounds (35796531 / 200000000) (699151 / 3906250) (Real.log (299 / 250)) := by
  have h := reflection_log_6396_neg
  have he : Real.log (299 / 250) = -Real.log (250 / 299) := by
    rw [show ((299 / 250) : ℝ) = ((250 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6397_neg : (218156009 / 1000000000) ≤ -Real.log (201 / 250) ∧
    -Real.log (201 / 250) ≤ (21815601 / 100000000) := by
  have h := checkLog_sound (w := (49 / 451)) (n := 12)
    (lo := (218156009 / 1000000000)) (hi := (21815601 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 201) = 1/(201 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6397 : Bounds (-21815601 / 100000000) (-218156009 / 1000000000) (Real.log (201 / 250)) := by
  have h := reflection_log_6397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6398_neg : (9799 / 50000000) ≤ -Real.log (250000 / 250049) ∧
    -Real.log (250000 / 250049) ≤ (195981 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 500049)) (n := 12)
    (lo := (9799 / 50000000)) (hi := (195981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250049 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250049 / 250000) = 1/(250000 / 250049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6398 : Bounds (9799 / 50000000) (195981 / 1000000000) (Real.log (250049 / 250000)) := by
  have h := reflection_log_6398_neg
  have he : Real.log (250049 / 250000) = -Real.log (250000 / 250049) := by
    rw [show ((250049 / 250000) : ℝ) = ((250000 / 250049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6399_neg : (196019 / 1000000000) ≤ -Real.log (249951 / 250000) ∧
    -Real.log (249951 / 250000) ≤ (9801 / 50000000) := by
  have h := checkLog_sound (w := (49 / 499951)) (n := 12)
    (lo := (196019 / 1000000000)) (hi := (9801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249951) = 1/(249951 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6399 : Bounds (-9801 / 50000000) (-196019 / 1000000000) (Real.log (249951 / 250000)) := by
  have h := reflection_log_6399_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0100 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6400_neg : (23495051 / 250000000) ≤ -Real.log (500000 / 549269) ∧
    -Real.log (500000 / 549269) ≤ (18796041 / 200000000) := by
  have h := checkLog_sound (w := (49269 / 1049269)) (n := 12)
    (lo := (23495051 / 250000000)) (hi := (18796041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549269 / 500000) = 1/(500000 / 549269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6400 : Bounds (23495051 / 250000000) (18796041 / 200000000) (Real.log (549269 / 500000)) := by
  have h := reflection_log_6400_neg
  have he : Real.log (549269 / 500000) = -Real.log (500000 / 549269) := by
    rw [show ((549269 / 500000) : ℝ) = ((500000 / 549269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6401_neg : (103737389 / 1000000000) ≤ -Real.log (450731 / 500000) ∧
    -Real.log (450731 / 500000) ≤ (10373739 / 100000000) := by
  have h := checkLog_sound (w := (49269 / 950731)) (n := 12)
    (lo := (103737389 / 1000000000)) (hi := (10373739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450731) = 1/(450731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6401 : Bounds (-10373739 / 100000000) (-103737389 / 1000000000) (Real.log (450731 / 500000)) := by
  have h := reflection_log_6401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6402_neg : (94204113 / 1000000000) ≤ -Real.log (31250 / 34337) ∧
    -Real.log (31250 / 34337) ≤ (47102057 / 500000000) := by
  have h := checkLog_sound (w := (3087 / 65587)) (n := 12)
    (lo := (94204113 / 1000000000)) (hi := (47102057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34337 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34337 / 31250) = 1/(31250 / 34337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6402 : Bounds (94204113 / 1000000000) (47102057 / 500000000) (Real.log (34337 / 31250)) := by
  have h := reflection_log_6402_neg
  have he : Real.log (34337 / 31250) = -Real.log (31250 / 34337) := by
    rw [show ((34337 / 31250) : ℝ) = ((31250 / 34337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6403_neg : (26002579 / 250000000) ≤ -Real.log (28163 / 31250) ∧
    -Real.log (28163 / 31250) ≤ (104010317 / 1000000000) := by
  have h := checkLog_sound (w := (3087 / 59413)) (n := 12)
    (lo := (26002579 / 250000000)) (hi := (104010317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28163) = 1/(28163 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6403 : Bounds (-104010317 / 1000000000) (-26002579 / 250000000) (Real.log (28163 / 31250)) := by
  have h := reflection_log_6403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6404_neg : (4903101 / 500000000) ≤ -Real.log (967032931 / 976562500) ∧
    -Real.log (967032931 / 976562500) ≤ (9806203 / 1000000000) := by
  have h := checkLog_sound (w := (9529569 / 1943595431)) (n := 12)
    (lo := (4903101 / 500000000)) (hi := (9806203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 967032931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 967032931) = 1/(967032931 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6404 : Bounds (-9806203 / 1000000000) (-4903101 / 500000000) (Real.log (967032931 / 976562500)) := by
  have h := reflection_log_6404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6405_neg : (19057 / 1953125) ≤ -Real.log (247572565639 / 250000000000) ∧
    -Real.log (247572565639 / 250000000000) ≤ (1951437 / 200000000) := by
  have h := checkLog_sound (w := (2427434361 / 497572565639)) (n := 12)
    (lo := (19057 / 1953125)) (hi := (1951437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247572565639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247572565639) = 1/(247572565639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6405 : Bounds (-1951437 / 200000000) (-19057 / 1953125) (Real.log (247572565639 / 250000000000)) := by
  have h := reflection_log_6405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6406_neg : (98858797 / 500000000) ≤ -Real.log (250000000000 / 304654550053) ∧
    -Real.log (250000000000 / 304654550053) ≤ (39543519 / 200000000) := by
  have h := checkLog_sound (w := (54654550053 / 554654550053)) (n := 12)
    (lo := (98858797 / 500000000)) (hi := (39543519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304654550053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304654550053 / 250000000000) = 1/(250000000000 / 304654550053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6406 : Bounds (98858797 / 500000000) (39543519 / 200000000) (Real.log (304654550053 / 250000000000)) := by
  have h := reflection_log_6406_neg
  have he : Real.log (304654550053 / 250000000000) = -Real.log (250000000000 / 304654550053) := by
    rw [show ((304654550053 / 250000000000) : ℝ) = ((250000000000 / 304654550053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6407_neg : (19821443 / 100000000) ≤ -Real.log (250000000000 / 304805951071) ∧
    -Real.log (250000000000 / 304805951071) ≤ (198214431 / 1000000000) := by
  have h := checkLog_sound (w := (54805951071 / 554805951071)) (n := 12)
    (lo := (19821443 / 100000000)) (hi := (198214431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304805951071 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304805951071 / 250000000000) = 1/(250000000000 / 304805951071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6407 : Bounds (19821443 / 100000000) (198214431 / 1000000000) (Real.log (304805951071 / 250000000000)) := by
  have h := reflection_log_6407_neg
  have he : Real.log (304805951071 / 250000000000) = -Real.log (250000000000 / 304805951071) := by
    rw [show ((304805951071 / 250000000000) : ℝ) = ((250000000000 / 304805951071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6408_neg : (396930679 / 1000000000) ≤ -Real.log (4000000000 / 5949011317) ∧
    -Real.log (4000000000 / 5949011317) ≤ (9923267 / 25000000) := by
  have h := checkLog_sound (w := (1949011317 / 9949011317)) (n := 12)
    (lo := (396930679 / 1000000000)) (hi := (9923267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949011317 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949011317 / 4000000000) = 1/(4000000000 / 5949011317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6408 : Bounds (396930679 / 1000000000) (9923267 / 25000000) (Real.log (5949011317 / 4000000000)) := by
  have h := reflection_log_6408_neg
  have he : Real.log (5949011317 / 4000000000) = -Real.log (4000000000 / 5949011317) := by
    rw [show ((5949011317 / 4000000000) : ℝ) = ((4000000000 / 5949011317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6409_neg : (79427733 / 200000000) ≤ -Real.log (3906250000 / 5810789801) ∧
    -Real.log (3906250000 / 5810789801) ≤ (198569333 / 500000000) := by
  have h := checkLog_sound (w := (1904539801 / 9717039801)) (n := 12)
    (lo := (79427733 / 200000000)) (hi := (198569333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5810789801 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5810789801 / 3906250000) = 1/(3906250000 / 5810789801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6409 : Bounds (79427733 / 200000000) (198569333 / 500000000) (Real.log (5810789801 / 3906250000)) := by
  have h := reflection_log_6409_neg
  have he : Real.log (5810789801 / 3906250000) = -Real.log (3906250000 / 5810789801) := by
    rw [show ((5810789801 / 3906250000) : ℝ) = ((3906250000 / 5810789801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6410_neg : (22383283 / 125000000) ≤ -Real.log (10000 / 11961) ∧
    -Real.log (10000 / 11961) ≤ (35813253 / 200000000) := by
  have h := checkLog_sound (w := (1961 / 21961)) (n := 12)
    (lo := (22383283 / 125000000)) (hi := (35813253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11961 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11961 / 10000) = 1/(10000 / 11961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6410 : Bounds (22383283 / 125000000) (35813253 / 200000000) (Real.log (11961 / 10000)) := by
  have h := reflection_log_6410_neg
  have he : Real.log (11961 / 10000) = -Real.log (10000 / 11961) := by
    rw [show ((11961 / 10000) : ℝ) = ((10000 / 11961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6411_neg : (43656079 / 200000000) ≤ -Real.log (8039 / 10000) ∧
    -Real.log (8039 / 10000) ≤ (54570099 / 250000000) := by
  have h := checkLog_sound (w := (1961 / 18039)) (n := 12)
    (lo := (43656079 / 200000000)) (hi := (54570099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8039) = 1/(8039 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6411 : Bounds (-54570099 / 250000000) (-43656079 / 200000000) (Real.log (8039 / 10000)) := by
  have h := reflection_log_6411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6412_neg : (2451 / 12500000) ≤ -Real.log (10000000 / 10001961) ∧
    -Real.log (10000000 / 10001961) ≤ (196081 / 1000000000) := by
  have h := checkLog_sound (w := (1961 / 20001961)) (n := 12)
    (lo := (2451 / 12500000)) (hi := (196081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001961 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001961 / 10000000) = 1/(10000000 / 10001961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6412 : Bounds (2451 / 12500000) (196081 / 1000000000) (Real.log (10001961 / 10000000)) := by
  have h := reflection_log_6412_neg
  have he : Real.log (10001961 / 10000000) = -Real.log (10000000 / 10001961) := by
    rw [show ((10001961 / 10000000) : ℝ) = ((10000000 / 10001961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6413_neg : (196119 / 1000000000) ≤ -Real.log (9998039 / 10000000) ∧
    -Real.log (9998039 / 10000000) ≤ (4903 / 25000000) := by
  have h := checkLog_sound (w := (1961 / 19998039)) (n := 12)
    (lo := (196119 / 1000000000)) (hi := (4903 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998039) = 1/(9998039 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6413 : Bounds (-4903 / 25000000) (-196119 / 1000000000) (Real.log (9998039 / 10000000)) := by
  have h := reflection_log_6413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6414_neg : (94026629 / 1000000000) ≤ -Real.log (1000000 / 1098589) ∧
    -Real.log (1000000 / 1098589) ≤ (9402663 / 100000000) := by
  have h := checkLog_sound (w := (98589 / 2098589)) (n := 12)
    (lo := (94026629 / 1000000000)) (hi := (9402663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098589 / 1000000) = 1/(1000000 / 1098589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6414 : Bounds (94026629 / 1000000000) (9402663 / 100000000) (Real.log (1098589 / 1000000)) := by
  have h := reflection_log_6414_neg
  have he : Real.log (1098589 / 1000000) = -Real.log (1000000 / 1098589) := by
    rw [show ((1098589 / 1000000) : ℝ) = ((1000000 / 1098589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6415_neg : (20758793 / 200000000) ≤ -Real.log (901411 / 1000000) ∧
    -Real.log (901411 / 1000000) ≤ (51896983 / 500000000) := by
  have h := checkLog_sound (w := (98589 / 1901411)) (n := 12)
    (lo := (20758793 / 200000000)) (hi := (51896983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901411) = 1/(901411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6415 : Bounds (-51896983 / 500000000) (-20758793 / 200000000) (Real.log (901411 / 1000000)) := by
  have h := reflection_log_6415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6416_neg : (94251437 / 1000000000) ≤ -Real.log (250000 / 274709) ∧
    -Real.log (250000 / 274709) ≤ (47125719 / 500000000) := by
  have h := checkLog_sound (w := (24709 / 524709)) (n := 12)
    (lo := (94251437 / 1000000000)) (hi := (47125719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274709 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274709 / 250000) = 1/(250000 / 274709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6416 : Bounds (94251437 / 1000000000) (47125719 / 500000000) (Real.log (274709 / 250000)) := by
  have h := reflection_log_6416_neg
  have he : Real.log (274709 / 250000) = -Real.log (250000 / 274709) := by
    rw [show ((274709 / 250000) : ℝ) = ((250000 / 274709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6417_neg : (104068017 / 1000000000) ≤ -Real.log (225291 / 250000) ∧
    -Real.log (225291 / 250000) ≤ (52034009 / 500000000) := by
  have h := checkLog_sound (w := (24709 / 475291)) (n := 12)
    (lo := (104068017 / 1000000000)) (hi := (52034009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225291) = 1/(225291 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6417 : Bounds (-52034009 / 500000000) (-104068017 / 1000000000) (Real.log (225291 / 250000)) := by
  have h := reflection_log_6417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6418_neg : (490829 / 50000000) ≤ -Real.log (61889465319 / 62500000000) ∧
    -Real.log (61889465319 / 62500000000) ≤ (9816581 / 1000000000) := by
  have h := checkLog_sound (w := (610534681 / 124389465319)) (n := 12)
    (lo := (490829 / 50000000)) (hi := (9816581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61889465319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61889465319) = 1/(61889465319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6418 : Bounds (-9816581 / 1000000000) (-490829 / 50000000) (Real.log (61889465319 / 62500000000)) := by
  have h := reflection_log_6418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6419_neg : (1220917 / 125000000) ≤ -Real.log (990280209079 / 1000000000000) ∧
    -Real.log (990280209079 / 1000000000000) ≤ (9767337 / 1000000000) := by
  have h := checkLog_sound (w := (9719790921 / 1990280209079)) (n := 12)
    (lo := (1220917 / 125000000)) (hi := (9767337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990280209079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990280209079) = 1/(990280209079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6419 : Bounds (-9767337 / 1000000000) (-1220917 / 125000000) (Real.log (990280209079 / 1000000000000)) := by
  have h := reflection_log_6419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6420_neg : (98910297 / 500000000) ≤ -Real.log (500000000000 / 609371862557) ∧
    -Real.log (500000000000 / 609371862557) ≤ (39564119 / 200000000) := by
  have h := checkLog_sound (w := (109371862557 / 1109371862557)) (n := 12)
    (lo := (98910297 / 500000000)) (hi := (39564119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609371862557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609371862557 / 500000000000) = 1/(500000000000 / 609371862557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6420 : Bounds (98910297 / 500000000) (39564119 / 200000000) (Real.log (609371862557 / 500000000000)) := by
  have h := reflection_log_6420_neg
  have he : Real.log (609371862557 / 500000000000) = -Real.log (500000000000 / 609371862557) := by
    rw [show ((609371862557 / 500000000000) : ℝ) = ((500000000000 / 609371862557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6421_neg : (39663891 / 200000000) ≤ -Real.log (250000000000 / 304837965121) ∧
    -Real.log (250000000000 / 304837965121) ≤ (6197483 / 31250000) := by
  have h := checkLog_sound (w := (54837965121 / 554837965121)) (n := 12)
    (lo := (39663891 / 200000000)) (hi := (6197483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304837965121 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304837965121 / 250000000000) = 1/(250000000000 / 304837965121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6421 : Bounds (39663891 / 200000000) (6197483 / 31250000) (Real.log (304837965121 / 250000000000)) := by
  have h := reflection_log_6421_neg
  have he : Real.log (304837965121 / 250000000000) = -Real.log (250000000000 / 304837965121) := by
    rw [show ((304837965121 / 250000000000) : ℝ) = ((250000000000 / 304837965121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6422_neg : (79427733 / 200000000) ≤ -Real.log (500000000000 / 743781094527) ∧
    -Real.log (500000000000 / 743781094527) ≤ (198569333 / 500000000) := by
  have h := checkLog_sound (w := (243781094527 / 1243781094527)) (n := 12)
    (lo := (79427733 / 200000000)) (hi := (198569333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743781094527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743781094527 / 500000000000) = 1/(500000000000 / 743781094527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6422 : Bounds (79427733 / 200000000) (198569333 / 500000000) (Real.log (743781094527 / 500000000000)) := by
  have h := reflection_log_6422_neg
  have he : Real.log (743781094527 / 500000000000) = -Real.log (500000000000 / 743781094527) := by
    rw [show ((743781094527 / 500000000000) : ℝ) = ((500000000000 / 743781094527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6423_neg : (397346659 / 1000000000) ≤ -Real.log (500000000000 / 743935812913) ∧
    -Real.log (500000000000 / 743935812913) ≤ (19867333 / 50000000) := by
  have h := checkLog_sound (w := (243935812913 / 1243935812913)) (n := 12)
    (lo := (397346659 / 1000000000)) (hi := (19867333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743935812913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743935812913 / 500000000000) = 1/(500000000000 / 743935812913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6423 : Bounds (397346659 / 1000000000) (19867333 / 50000000) (Real.log (743935812913 / 500000000000)) := by
  have h := reflection_log_6423_neg
  have he : Real.log (743935812913 / 500000000000) = -Real.log (500000000000 / 743935812913) := by
    rw [show ((743935812913 / 500000000000) : ℝ) = ((500000000000 / 743935812913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6424_neg : (35829973 / 200000000) ≤ -Real.log (5000 / 5981) ∧
    -Real.log (5000 / 5981) ≤ (89574933 / 500000000) := by
  have h := checkLog_sound (w := (981 / 10981)) (n := 12)
    (lo := (35829973 / 200000000)) (hi := (89574933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5981 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5981 / 5000) = 1/(5000 / 5981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6424 : Bounds (35829973 / 200000000) (89574933 / 500000000) (Real.log (5981 / 5000)) := by
  have h := reflection_log_6424_neg
  have he : Real.log (5981 / 5000) = -Real.log (5000 / 5981) := by
    rw [show ((5981 / 5000) : ℝ) = ((5000 / 5981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6425_neg : (54601199 / 250000000) ≤ -Real.log (4019 / 5000) ∧
    -Real.log (4019 / 5000) ≤ (218404797 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 9019)) (n := 12)
    (lo := (54601199 / 250000000)) (hi := (218404797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4019) = 1/(4019 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6425 : Bounds (-218404797 / 1000000000) (-54601199 / 250000000) (Real.log (4019 / 5000)) := by
  have h := reflection_log_6425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6426_neg : (9809 / 50000000) ≤ -Real.log (5000000 / 5000981) ∧
    -Real.log (5000000 / 5000981) ≤ (196181 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 10000981)) (n := 12)
    (lo := (9809 / 50000000)) (hi := (196181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000981 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000981 / 5000000) = 1/(5000000 / 5000981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6426 : Bounds (9809 / 50000000) (196181 / 1000000000) (Real.log (5000981 / 5000000)) := by
  have h := reflection_log_6426_neg
  have he : Real.log (5000981 / 5000000) = -Real.log (5000000 / 5000981) := by
    rw [show ((5000981 / 5000000) : ℝ) = ((5000000 / 5000981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6427_neg : (196219 / 1000000000) ≤ -Real.log (4999019 / 5000000) ∧
    -Real.log (4999019 / 5000000) ≤ (9811 / 50000000) := by
  have h := checkLog_sound (w := (981 / 9999019)) (n := 12)
    (lo := (196219 / 1000000000)) (hi := (9811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999019) = 1/(4999019 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6427 : Bounds (-9811 / 50000000) (-196219 / 1000000000) (Real.log (4999019 / 5000000)) := by
  have h := reflection_log_6427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6428_neg : (94073051 / 1000000000) ≤ -Real.log (12500 / 13733) ∧
    -Real.log (12500 / 13733) ≤ (23518263 / 250000000) := by
  have h := checkLog_sound (w := (1233 / 26233)) (n := 12)
    (lo := (94073051 / 1000000000)) (hi := (23518263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13733 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13733 / 12500) = 1/(12500 / 13733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6428 : Bounds (94073051 / 1000000000) (23518263 / 250000000) (Real.log (13733 / 12500)) := by
  have h := reflection_log_6428_neg
  have he : Real.log (13733 / 12500) = -Real.log (12500 / 13733) := by
    rw [show ((13733 / 12500) : ℝ) = ((12500 / 13733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6429_neg : (20770109 / 200000000) ≤ -Real.log (11267 / 12500) ∧
    -Real.log (11267 / 12500) ≤ (51925273 / 500000000) := by
  have h := checkLog_sound (w := (1233 / 23767)) (n := 12)
    (lo := (20770109 / 200000000)) (hi := (51925273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11267) = 1/(11267 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6429 : Bounds (-51925273 / 500000000) (-20770109 / 200000000) (Real.log (11267 / 12500)) := by
  have h := reflection_log_6429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6430_neg : (94297849 / 1000000000) ≤ -Real.log (1000000 / 1098887) ∧
    -Real.log (1000000 / 1098887) ≤ (1885957 / 20000000) := by
  have h := checkLog_sound (w := (98887 / 2098887)) (n := 12)
    (lo := (94297849 / 1000000000)) (hi := (1885957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098887 / 1000000) = 1/(1000000 / 1098887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6430 : Bounds (94297849 / 1000000000) (1885957 / 20000000) (Real.log (1098887 / 1000000)) := by
  have h := reflection_log_6430_neg
  have he : Real.log (1098887 / 1000000) = -Real.log (1000000 / 1098887) := by
    rw [show ((1098887 / 1000000) : ℝ) = ((1000000 / 1098887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6431_neg : (104124613 / 1000000000) ≤ -Real.log (901113 / 1000000) ∧
    -Real.log (901113 / 1000000) ≤ (52062307 / 500000000) := by
  have h := checkLog_sound (w := (98887 / 1901113)) (n := 12)
    (lo := (104124613 / 1000000000)) (hi := (52062307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901113) = 1/(901113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6431 : Bounds (-52062307 / 500000000) (-104124613 / 1000000000) (Real.log (901113 / 1000000)) := by
  have h := reflection_log_6431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6432_neg : (9826763 / 1000000000) ≤ -Real.log (990221361231 / 1000000000000) ∧
    -Real.log (990221361231 / 1000000000000) ≤ (2456691 / 250000000) := by
  have h := checkLog_sound (w := (9778638769 / 1990221361231)) (n := 12)
    (lo := (9826763 / 1000000000)) (hi := (2456691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990221361231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990221361231) = 1/(990221361231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6432 : Bounds (-2456691 / 250000000) (-9826763 / 1000000000) (Real.log (990221361231 / 1000000000000)) := by
  have h := reflection_log_6432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6433_neg : (9777493 / 1000000000) ≤ -Real.log (154729711 / 156250000) ∧
    -Real.log (154729711 / 156250000) ≤ (4888747 / 500000000) := by
  have h := checkLog_sound (w := (1520289 / 310979711)) (n := 12)
    (lo := (9777493 / 1000000000)) (hi := (4888747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 154729711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 154729711) = 1/(154729711 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6433 : Bounds (-4888747 / 500000000) (-9777493 / 1000000000) (Real.log (154729711 / 156250000)) := by
  have h := reflection_log_6433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6434_neg : (49480899 / 250000000) ≤ -Real.log (500000000000 / 609434632111) ∧
    -Real.log (500000000000 / 609434632111) ≤ (197923597 / 1000000000) := by
  have h := checkLog_sound (w := (109434632111 / 1109434632111)) (n := 12)
    (lo := (49480899 / 250000000)) (hi := (197923597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609434632111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609434632111 / 500000000000) = 1/(500000000000 / 609434632111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6434 : Bounds (49480899 / 250000000) (197923597 / 1000000000) (Real.log (609434632111 / 500000000000)) := by
  have h := reflection_log_6434_neg
  have he : Real.log (609434632111 / 500000000000) = -Real.log (500000000000 / 609434632111) := by
    rw [show ((609434632111 / 500000000000) : ℝ) = ((500000000000 / 609434632111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6435_neg : (99211231 / 500000000) ≤ -Real.log (50000000000 / 60973873421) ∧
    -Real.log (50000000000 / 60973873421) ≤ (198422463 / 1000000000) := by
  have h := checkLog_sound (w := (10973873421 / 110973873421)) (n := 12)
    (lo := (99211231 / 500000000)) (hi := (198422463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60973873421 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60973873421 / 50000000000) = 1/(50000000000 / 60973873421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6435 : Bounds (99211231 / 500000000) (198422463 / 1000000000) (Real.log (60973873421 / 50000000000)) := by
  have h := reflection_log_6435_neg
  have he : Real.log (60973873421 / 50000000000) = -Real.log (50000000000 / 60973873421) := by
    rw [show ((60973873421 / 50000000000) : ℝ) = ((50000000000 / 60973873421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6436_neg : (397346659 / 1000000000) ≤ -Real.log (31250000000 / 46495988307) ∧
    -Real.log (31250000000 / 46495988307) ≤ (19867333 / 50000000) := by
  have h := checkLog_sound (w := (15245988307 / 77745988307)) (n := 12)
    (lo := (397346659 / 1000000000)) (hi := (19867333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46495988307 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46495988307 / 31250000000) = 1/(31250000000 / 46495988307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6436 : Bounds (397346659 / 1000000000) (19867333 / 50000000) (Real.log (46495988307 / 31250000000)) := by
  have h := reflection_log_6436_neg
  have he : Real.log (46495988307 / 31250000000) = -Real.log (31250000000 / 46495988307) := by
    rw [show ((46495988307 / 31250000000) : ℝ) = ((31250000000 / 46495988307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6437_neg : (198777331 / 500000000) ≤ -Real.log (250000000000 / 372045284897) ∧
    -Real.log (250000000000 / 372045284897) ≤ (397554663 / 1000000000) := by
  have h := checkLog_sound (w := (122045284897 / 622045284897)) (n := 12)
    (lo := (198777331 / 500000000)) (hi := (397554663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372045284897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372045284897 / 250000000000) = 1/(250000000000 / 372045284897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6437 : Bounds (198777331 / 500000000) (397554663 / 1000000000) (Real.log (372045284897 / 250000000000)) := by
  have h := reflection_log_6437_neg
  have he : Real.log (372045284897 / 250000000000) = -Real.log (250000000000 / 372045284897) := by
    rw [show ((372045284897 / 250000000000) : ℝ) = ((250000000000 / 372045284897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6438_neg : (8961673 / 50000000) ≤ -Real.log (10000 / 11963) ∧
    -Real.log (10000 / 11963) ≤ (179233461 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 21963)) (n := 12)
    (lo := (8961673 / 50000000)) (hi := (179233461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11963 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11963 / 10000) = 1/(10000 / 11963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6438 : Bounds (8961673 / 50000000) (179233461 / 1000000000) (Real.log (11963 / 10000)) := by
  have h := reflection_log_6438_neg
  have he : Real.log (11963 / 10000) = -Real.log (10000 / 11963) := by
    rw [show ((11963 / 10000) : ℝ) = ((10000 / 11963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6439_neg : (218529213 / 1000000000) ≤ -Real.log (8037 / 10000) ∧
    -Real.log (8037 / 10000) ≤ (109264607 / 500000000) := by
  have h := checkLog_sound (w := (1963 / 18037)) (n := 12)
    (lo := (218529213 / 1000000000)) (hi := (109264607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8037) = 1/(8037 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6439 : Bounds (-109264607 / 500000000) (-218529213 / 1000000000) (Real.log (8037 / 10000)) := by
  have h := reflection_log_6439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6440_neg : (4907 / 25000000) ≤ -Real.log (10000000 / 10001963) ∧
    -Real.log (10000000 / 10001963) ≤ (196281 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 20001963)) (n := 12)
    (lo := (4907 / 25000000)) (hi := (196281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001963 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001963 / 10000000) = 1/(10000000 / 10001963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6440 : Bounds (4907 / 25000000) (196281 / 1000000000) (Real.log (10001963 / 10000000)) := by
  have h := reflection_log_6440_neg
  have he : Real.log (10001963 / 10000000) = -Real.log (10000000 / 10001963) := by
    rw [show ((10001963 / 10000000) : ℝ) = ((10000000 / 10001963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6441_neg : (196319 / 1000000000) ≤ -Real.log (9998037 / 10000000) ∧
    -Real.log (9998037 / 10000000) ≤ (1227 / 6250000) := by
  have h := checkLog_sound (w := (1963 / 19998037)) (n := 12)
    (lo := (196319 / 1000000000)) (hi := (1227 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998037) = 1/(9998037 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6441 : Bounds (-1227 / 6250000) (-196319 / 1000000000) (Real.log (9998037 / 10000000)) := by
  have h := reflection_log_6441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6442_neg : (94119471 / 1000000000) ≤ -Real.log (1000000 / 1098691) ∧
    -Real.log (1000000 / 1098691) ≤ (5882467 / 62500000) := by
  have h := checkLog_sound (w := (98691 / 2098691)) (n := 12)
    (lo := (94119471 / 1000000000)) (hi := (5882467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098691 / 1000000) = 1/(1000000 / 1098691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6442 : Bounds (94119471 / 1000000000) (5882467 / 62500000) (Real.log (1098691 / 1000000)) := by
  have h := reflection_log_6442_neg
  have he : Real.log (1098691 / 1000000) = -Real.log (1000000 / 1098691) := by
    rw [show ((1098691 / 1000000) : ℝ) = ((1000000 / 1098691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6443_neg : (103907127 / 1000000000) ≤ -Real.log (901309 / 1000000) ∧
    -Real.log (901309 / 1000000) ≤ (12988391 / 125000000) := by
  have h := checkLog_sound (w := (98691 / 1901309)) (n := 12)
    (lo := (103907127 / 1000000000)) (hi := (12988391 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901309) = 1/(901309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6443 : Bounds (-12988391 / 125000000) (-103907127 / 1000000000) (Real.log (901309 / 1000000)) := by
  have h := reflection_log_6443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6444_neg : (47172129 / 500000000) ≤ -Real.log (500000 / 549469) ∧
    -Real.log (500000 / 549469) ≤ (94344259 / 1000000000) := by
  have h := checkLog_sound (w := (49469 / 1049469)) (n := 12)
    (lo := (47172129 / 500000000)) (hi := (94344259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549469 / 500000) = 1/(500000 / 549469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6444 : Bounds (47172129 / 500000000) (94344259 / 1000000000) (Real.log (549469 / 500000)) := by
  have h := reflection_log_6444_neg
  have he : Real.log (549469 / 500000) = -Real.log (500000 / 549469) := by
    rw [show ((549469 / 500000) : ℝ) = ((500000 / 549469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6445_neg : (104181211 / 1000000000) ≤ -Real.log (450531 / 500000) ∧
    -Real.log (450531 / 500000) ≤ (26045303 / 250000000) := by
  have h := checkLog_sound (w := (49469 / 950531)) (n := 12)
    (lo := (104181211 / 1000000000)) (hi := (26045303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450531) = 1/(450531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6445 : Bounds (-26045303 / 250000000) (-104181211 / 1000000000) (Real.log (450531 / 500000)) := by
  have h := reflection_log_6445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6446_neg : (1229619 / 125000000) ≤ -Real.log (247552818039 / 250000000000) ∧
    -Real.log (247552818039 / 250000000000) ≤ (9836953 / 1000000000) := by
  have h := checkLog_sound (w := (2447181961 / 497552818039)) (n := 12)
    (lo := (1229619 / 125000000)) (hi := (9836953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247552818039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247552818039) = 1/(247552818039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6446 : Bounds (-9836953 / 1000000000) (-1229619 / 125000000) (Real.log (247552818039 / 250000000000)) := by
  have h := reflection_log_6446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6447_neg : (1223457 / 125000000) ≤ -Real.log (990260086519 / 1000000000000) ∧
    -Real.log (990260086519 / 1000000000000) ≤ (9787657 / 1000000000) := by
  have h := checkLog_sound (w := (9739913481 / 1990260086519)) (n := 12)
    (lo := (1223457 / 125000000)) (hi := (9787657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990260086519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990260086519) = 1/(990260086519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6447 : Bounds (-9787657 / 1000000000) (-1223457 / 125000000) (Real.log (990260086519 / 1000000000000)) := by
  have h := reflection_log_6447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6448_neg : (198026599 / 1000000000) ≤ -Real.log (1953125000 / 2380849253) ∧
    -Real.log (1953125000 / 2380849253) ≤ (990133 / 5000000) := by
  have h := checkLog_sound (w := (427724253 / 4333974253)) (n := 12)
    (lo := (198026599 / 1000000000)) (hi := (990133 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2380849253 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2380849253 / 1953125000) = 1/(1953125000 / 2380849253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6448 : Bounds (198026599 / 1000000000) (990133 / 5000000) (Real.log (2380849253 / 1953125000)) := by
  have h := reflection_log_6448_neg
  have he : Real.log (2380849253 / 1953125000) = -Real.log (1953125000 / 2380849253) := by
    rw [show ((2380849253 / 1953125000) : ℝ) = ((1953125000 / 2380849253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6449_neg : (19852547 / 100000000) ≤ -Real.log (62500000000 / 76225193161) ∧
    -Real.log (62500000000 / 76225193161) ≤ (198525471 / 1000000000) := by
  have h := checkLog_sound (w := (13725193161 / 138725193161)) (n := 12)
    (lo := (19852547 / 100000000)) (hi := (198525471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76225193161 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76225193161 / 62500000000) = 1/(62500000000 / 76225193161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6449 : Bounds (19852547 / 100000000) (198525471 / 1000000000) (Real.log (76225193161 / 62500000000)) := by
  have h := reflection_log_6449_neg
  have he : Real.log (76225193161 / 62500000000) = -Real.log (62500000000 / 76225193161) := by
    rw [show ((76225193161 / 62500000000) : ℝ) = ((62500000000 / 76225193161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6450_neg : (198777331 / 500000000) ≤ -Real.log (500000000000 / 744090569793) ∧
    -Real.log (500000000000 / 744090569793) ≤ (397554663 / 1000000000) := by
  have h := checkLog_sound (w := (244090569793 / 1244090569793)) (n := 12)
    (lo := (198777331 / 500000000)) (hi := (397554663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744090569793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744090569793 / 500000000000) = 1/(500000000000 / 744090569793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6450 : Bounds (198777331 / 500000000) (397554663 / 1000000000) (Real.log (744090569793 / 500000000000)) := by
  have h := reflection_log_6450_neg
  have he : Real.log (744090569793 / 500000000000) = -Real.log (500000000000 / 744090569793) := by
    rw [show ((744090569793 / 500000000000) : ℝ) = ((500000000000 / 744090569793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6451_neg : (397762673 / 1000000000) ≤ -Real.log (500000000000 / 744245365187) ∧
    -Real.log (500000000000 / 744245365187) ≤ (198881337 / 500000000) := by
  have h := checkLog_sound (w := (244245365187 / 1244245365187)) (n := 12)
    (lo := (397762673 / 1000000000)) (hi := (198881337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744245365187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744245365187 / 500000000000) = 1/(500000000000 / 744245365187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6451 : Bounds (397762673 / 1000000000) (198881337 / 500000000) (Real.log (744245365187 / 500000000000)) := by
  have h := reflection_log_6451_neg
  have he : Real.log (744245365187 / 500000000000) = -Real.log (500000000000 / 744245365187) := by
    rw [show ((744245365187 / 500000000000) : ℝ) = ((500000000000 / 744245365187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6452_neg : (179317047 / 1000000000) ≤ -Real.log (2500 / 2991) ∧
    -Real.log (2500 / 2991) ≤ (22414631 / 125000000) := by
  have h := checkLog_sound (w := (491 / 5491)) (n := 12)
    (lo := (179317047 / 1000000000)) (hi := (22414631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2991 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2991 / 2500) = 1/(2500 / 2991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6452 : Bounds (179317047 / 1000000000) (22414631 / 125000000) (Real.log (2991 / 2500)) := by
  have h := reflection_log_6452_neg
  have he : Real.log (2991 / 2500) = -Real.log (2500 / 2991) := by
    rw [show ((2991 / 2500) : ℝ) = ((2500 / 2991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6453_neg : (109326823 / 500000000) ≤ -Real.log (2009 / 2500) ∧
    -Real.log (2009 / 2500) ≤ (218653647 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 4509)) (n := 12)
    (lo := (109326823 / 500000000)) (hi := (218653647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2009) = 1/(2009 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6453 : Bounds (-218653647 / 1000000000) (-109326823 / 500000000) (Real.log (2009 / 2500)) := by
  have h := reflection_log_6453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6454_neg : (9819 / 50000000) ≤ -Real.log (2500000 / 2500491) ∧
    -Real.log (2500000 / 2500491) ≤ (196381 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 5000491)) (n := 12)
    (lo := (9819 / 50000000)) (hi := (196381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500491 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500491 / 2500000) = 1/(2500000 / 2500491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6454 : Bounds (9819 / 50000000) (196381 / 1000000000) (Real.log (2500491 / 2500000)) := by
  have h := reflection_log_6454_neg
  have he : Real.log (2500491 / 2500000) = -Real.log (2500000 / 2500491) := by
    rw [show ((2500491 / 2500000) : ℝ) = ((2500000 / 2500491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6455_neg : (196419 / 1000000000) ≤ -Real.log (2499509 / 2500000) ∧
    -Real.log (2499509 / 2500000) ≤ (9821 / 50000000) := by
  have h := checkLog_sound (w := (491 / 4999509)) (n := 12)
    (lo := (196419 / 1000000000)) (hi := (9821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499509) = 1/(2499509 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6455 : Bounds (-9821 / 50000000) (-196419 / 1000000000) (Real.log (2499509 / 2500000)) := by
  have h := reflection_log_6455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6456_neg : (735671 / 7812500) ≤ -Real.log (500000 / 549371) ∧
    -Real.log (500000 / 549371) ≤ (94165889 / 1000000000) := by
  have h := checkLog_sound (w := (49371 / 1049371)) (n := 12)
    (lo := (735671 / 7812500)) (hi := (94165889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549371 / 500000) = 1/(500000 / 549371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6456 : Bounds (735671 / 7812500) (94165889 / 1000000000) (Real.log (549371 / 500000)) := by
  have h := reflection_log_6456_neg
  have he : Real.log (549371 / 500000) = -Real.log (500000 / 549371) := by
    rw [show ((549371 / 500000) : ℝ) = ((500000 / 549371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6457_neg : (103963713 / 1000000000) ≤ -Real.log (450629 / 500000) ∧
    -Real.log (450629 / 500000) ≤ (51981857 / 500000000) := by
  have h := checkLog_sound (w := (49371 / 950629)) (n := 12)
    (lo := (103963713 / 1000000000)) (hi := (51981857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450629) = 1/(450629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6457 : Bounds (-51981857 / 500000000) (-103963713 / 1000000000) (Real.log (450629 / 500000)) := by
  have h := reflection_log_6457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6458_neg : (47195333 / 500000000) ≤ -Real.log (1000000 / 1098989) ∧
    -Real.log (1000000 / 1098989) ≤ (94390667 / 1000000000) := by
  have h := checkLog_sound (w := (98989 / 2098989)) (n := 12)
    (lo := (47195333 / 500000000)) (hi := (94390667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098989 / 1000000) = 1/(1000000 / 1098989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6458 : Bounds (47195333 / 500000000) (94390667 / 1000000000) (Real.log (1098989 / 1000000)) := by
  have h := reflection_log_6458_neg
  have he : Real.log (1098989 / 1000000) = -Real.log (1000000 / 1098989) := by
    rw [show ((1098989 / 1000000) : ℝ) = ((1000000 / 1098989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6459_neg : (26059453 / 250000000) ≤ -Real.log (901011 / 1000000) ∧
    -Real.log (901011 / 1000000) ≤ (104237813 / 1000000000) := by
  have h := checkLog_sound (w := (98989 / 1901011)) (n := 12)
    (lo := (26059453 / 250000000)) (hi := (104237813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901011) = 1/(901011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6459 : Bounds (-104237813 / 1000000000) (-26059453 / 250000000) (Real.log (901011 / 1000000)) := by
  have h := reflection_log_6459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6460_neg : (4923573 / 500000000) ≤ -Real.log (990201177879 / 1000000000000) ∧
    -Real.log (990201177879 / 1000000000000) ≤ (9847147 / 1000000000) := by
  have h := checkLog_sound (w := (9798822121 / 1990201177879)) (n := 12)
    (lo := (4923573 / 500000000)) (hi := (9847147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990201177879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990201177879) = 1/(990201177879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6460 : Bounds (-9847147 / 1000000000) (-4923573 / 500000000) (Real.log (990201177879 / 1000000000000)) := by
  have h := reflection_log_6460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6461_neg : (153091 / 15625000) ≤ -Real.log (247562504359 / 250000000000) ∧
    -Real.log (247562504359 / 250000000000) ≤ (391913 / 40000000) := by
  have h := checkLog_sound (w := (2437495641 / 497562504359)) (n := 12)
    (lo := (153091 / 15625000)) (hi := (391913 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247562504359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247562504359) = 1/(247562504359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6461 : Bounds (-391913 / 40000000) (-153091 / 15625000) (Real.log (247562504359 / 250000000000)) := by
  have h := reflection_log_6461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6462_neg : (99064801 / 500000000) ≤ -Real.log (50000000000 / 60956019253) ∧
    -Real.log (50000000000 / 60956019253) ≤ (198129603 / 1000000000) := by
  have h := checkLog_sound (w := (10956019253 / 110956019253)) (n := 12)
    (lo := (99064801 / 500000000)) (hi := (198129603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60956019253 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60956019253 / 50000000000) = 1/(50000000000 / 60956019253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6462 : Bounds (99064801 / 500000000) (198129603 / 1000000000) (Real.log (60956019253 / 50000000000)) := by
  have h := reflection_log_6462_neg
  have he : Real.log (60956019253 / 50000000000) = -Real.log (50000000000 / 60956019253) := by
    rw [show ((60956019253 / 50000000000) : ℝ) = ((50000000000 / 60956019253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6463_neg : (198628479 / 1000000000) ≤ -Real.log (500000000000 / 609864363477) ∧
    -Real.log (500000000000 / 609864363477) ≤ (310357 / 1562500) := by
  have h := checkLog_sound (w := (109864363477 / 1109864363477)) (n := 12)
    (lo := (198628479 / 1000000000)) (hi := (310357 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609864363477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609864363477 / 500000000000) = 1/(500000000000 / 609864363477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6463 : Bounds (198628479 / 1000000000) (310357 / 1562500) (Real.log (609864363477 / 500000000000)) := by
  have h := reflection_log_6463_neg
  have he : Real.log (609864363477 / 500000000000) = -Real.log (500000000000 / 609864363477) := by
    rw [show ((609864363477 / 500000000000) : ℝ) = ((500000000000 / 609864363477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0101 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6464_neg : (397762673 / 1000000000) ≤ -Real.log (250000000000 / 372122682593) ∧
    -Real.log (250000000000 / 372122682593) ≤ (198881337 / 500000000) := by
  have h := checkLog_sound (w := (122122682593 / 622122682593)) (n := 12)
    (lo := (397762673 / 1000000000)) (hi := (198881337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372122682593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372122682593 / 250000000000) = 1/(250000000000 / 372122682593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6464 : Bounds (397762673 / 1000000000) (198881337 / 500000000) (Real.log (372122682593 / 250000000000)) := by
  have h := reflection_log_6464_neg
  have he : Real.log (372122682593 / 250000000000) = -Real.log (250000000000 / 372122682593) := by
    rw [show ((372122682593 / 250000000000) : ℝ) = ((250000000000 / 372122682593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6465_neg : (397970693 / 1000000000) ≤ -Real.log (100000000000 / 148880039821) ∧
    -Real.log (100000000000 / 148880039821) ≤ (198985347 / 500000000) := by
  have h := checkLog_sound (w := (48880039821 / 248880039821)) (n := 12)
    (lo := (397970693 / 1000000000)) (hi := (198985347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148880039821 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148880039821 / 100000000000) = 1/(100000000000 / 148880039821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6465 : Bounds (397970693 / 1000000000) (198985347 / 500000000) (Real.log (148880039821 / 100000000000)) := by
  have h := reflection_log_6465_neg
  have he : Real.log (148880039821 / 100000000000) = -Real.log (100000000000 / 148880039821) := by
    rw [show ((148880039821 / 100000000000) : ℝ) = ((100000000000 / 148880039821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6466_neg : (44850157 / 250000000) ≤ -Real.log (2000 / 2393) ∧
    -Real.log (2000 / 2393) ≤ (179400629 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4393)) (n := 12)
    (lo := (44850157 / 250000000)) (hi := (179400629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2393 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2393 / 2000) = 1/(2000 / 2393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6466 : Bounds (44850157 / 250000000) (179400629 / 1000000000) (Real.log (2393 / 2000)) := by
  have h := reflection_log_6466_neg
  have he : Real.log (2393 / 2000) = -Real.log (2000 / 2393) := by
    rw [show ((2393 / 2000) : ℝ) = ((2000 / 2393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6467_neg : (218778093 / 1000000000) ≤ -Real.log (1607 / 2000) ∧
    -Real.log (1607 / 2000) ≤ (109389047 / 500000000) := by
  have h := checkLog_sound (w := (393 / 3607)) (n := 12)
    (lo := (218778093 / 1000000000)) (hi := (109389047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1607) = 1/(1607 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6467 : Bounds (-109389047 / 500000000) (-218778093 / 1000000000) (Real.log (1607 / 2000)) := by
  have h := reflection_log_6467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6468_neg : (307 / 1562500) ≤ -Real.log (2000000 / 2000393) ∧
    -Real.log (2000000 / 2000393) ≤ (196481 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4000393)) (n := 12)
    (lo := (307 / 1562500)) (hi := (196481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000393 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000393 / 2000000) = 1/(2000000 / 2000393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6468 : Bounds (307 / 1562500) (196481 / 1000000000) (Real.log (2000393 / 2000000)) := by
  have h := reflection_log_6468_neg
  have he : Real.log (2000393 / 2000000) = -Real.log (2000000 / 2000393) := by
    rw [show ((2000393 / 2000000) : ℝ) = ((2000000 / 2000393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6469_neg : (196519 / 1000000000) ≤ -Real.log (1999607 / 2000000) ∧
    -Real.log (1999607 / 2000000) ≤ (4913 / 25000000) := by
  have h := checkLog_sound (w := (393 / 3999607)) (n := 12)
    (lo := (196519 / 1000000000)) (hi := (4913 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999607) = 1/(1999607 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6469 : Bounds (-4913 / 25000000) (-196519 / 1000000000) (Real.log (1999607 / 2000000)) := by
  have h := reflection_log_6469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6470_neg : (5888269 / 62500000) ≤ -Real.log (1000000 / 1098793) ∧
    -Real.log (1000000 / 1098793) ≤ (18842461 / 200000000) := by
  have h := checkLog_sound (w := (98793 / 2098793)) (n := 12)
    (lo := (5888269 / 62500000)) (hi := (18842461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098793 / 1000000) = 1/(1000000 / 1098793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6470 : Bounds (5888269 / 62500000) (18842461 / 200000000) (Real.log (1098793 / 1000000)) := by
  have h := reflection_log_6470_neg
  have he : Real.log (1098793 / 1000000) = -Real.log (1000000 / 1098793) := by
    rw [show ((1098793 / 1000000) : ℝ) = ((1000000 / 1098793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6471_neg : (104020303 / 1000000000) ≤ -Real.log (901207 / 1000000) ∧
    -Real.log (901207 / 1000000) ≤ (6501269 / 62500000) := by
  have h := checkLog_sound (w := (98793 / 1901207)) (n := 12)
    (lo := (104020303 / 1000000000)) (hi := (6501269 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901207) = 1/(901207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6471 : Bounds (-6501269 / 62500000) (-104020303 / 1000000000) (Real.log (901207 / 1000000)) := by
  have h := reflection_log_6471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6472_neg : (94437071 / 1000000000) ≤ -Real.log (6250 / 6869) ∧
    -Real.log (6250 / 6869) ≤ (5902317 / 62500000) := by
  have h := checkLog_sound (w := (619 / 13119)) (n := 12)
    (lo := (94437071 / 1000000000)) (hi := (5902317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6869 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6869 / 6250) = 1/(6250 / 6869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6472 : Bounds (94437071 / 1000000000) (5902317 / 62500000) (Real.log (6869 / 6250)) := by
  have h := reflection_log_6472_neg
  have he : Real.log (6869 / 6250) = -Real.log (6250 / 6869) := by
    rw [show ((6869 / 6250) : ℝ) = ((6250 / 6869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6473_neg : (104294417 / 1000000000) ≤ -Real.log (5631 / 6250) ∧
    -Real.log (5631 / 6250) ≤ (52147209 / 500000000) := by
  have h := checkLog_sound (w := (619 / 11881)) (n := 12)
    (lo := (104294417 / 1000000000)) (hi := (52147209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5631) = 1/(5631 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6473 : Bounds (-52147209 / 500000000) (-104294417 / 1000000000) (Real.log (5631 / 6250)) := by
  have h := reflection_log_6473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6474_neg : (1971469 / 200000000) ≤ -Real.log (38679339 / 39062500) ∧
    -Real.log (38679339 / 39062500) ≤ (4928673 / 500000000) := by
  have h := checkLog_sound (w := (383161 / 77741839)) (n := 12)
    (lo := (1971469 / 200000000)) (hi := (4928673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38679339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38679339) = 1/(38679339 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6474 : Bounds (-4928673 / 500000000) (-1971469 / 200000000) (Real.log (38679339 / 39062500)) := by
  have h := reflection_log_6474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6475_neg : (4903999 / 500000000) ≤ -Real.log (990239943151 / 1000000000000) ∧
    -Real.log (990239943151 / 1000000000000) ≤ (9807999 / 1000000000) := by
  have h := checkLog_sound (w := (9760056849 / 1990239943151)) (n := 12)
    (lo := (4903999 / 500000000)) (hi := (9807999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990239943151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990239943151) = 1/(990239943151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6475 : Bounds (-9807999 / 1000000000) (-4903999 / 500000000) (Real.log (990239943151 / 1000000000000)) := by
  have h := reflection_log_6475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6476_neg : (198232607 / 1000000000) ≤ -Real.log (250000000000 / 304811491699) ∧
    -Real.log (250000000000 / 304811491699) ≤ (6194769 / 31250000) := by
  have h := checkLog_sound (w := (54811491699 / 554811491699)) (n := 12)
    (lo := (198232607 / 1000000000)) (hi := (6194769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304811491699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304811491699 / 250000000000) = 1/(250000000000 / 304811491699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6476 : Bounds (198232607 / 1000000000) (6194769 / 31250000) (Real.log (304811491699 / 250000000000)) := by
  have h := reflection_log_6476_neg
  have he : Real.log (304811491699 / 250000000000) = -Real.log (250000000000 / 304811491699) := by
    rw [show ((304811491699 / 250000000000) : ℝ) = ((250000000000 / 304811491699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6477_neg : (6210359 / 31250000) ≤ -Real.log (500000000000 / 609927188777) ∧
    -Real.log (500000000000 / 609927188777) ≤ (198731489 / 1000000000) := by
  have h := checkLog_sound (w := (109927188777 / 1109927188777)) (n := 12)
    (lo := (6210359 / 31250000)) (hi := (198731489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609927188777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609927188777 / 500000000000) = 1/(500000000000 / 609927188777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6477 : Bounds (6210359 / 31250000) (198731489 / 1000000000) (Real.log (609927188777 / 500000000000)) := by
  have h := reflection_log_6477_neg
  have he : Real.log (609927188777 / 500000000000) = -Real.log (500000000000 / 609927188777) := by
    rw [show ((609927188777 / 500000000000) : ℝ) = ((500000000000 / 609927188777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6478_neg : (397970693 / 1000000000) ≤ -Real.log (7812500000 / 11631253111) ∧
    -Real.log (7812500000 / 11631253111) ≤ (198985347 / 500000000) := by
  have h := checkLog_sound (w := (3818753111 / 19443753111)) (n := 12)
    (lo := (397970693 / 1000000000)) (hi := (198985347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11631253111 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11631253111 / 7812500000) = 1/(7812500000 / 11631253111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6478 : Bounds (397970693 / 1000000000) (198985347 / 500000000) (Real.log (11631253111 / 7812500000)) := by
  have h := reflection_log_6478_neg
  have he : Real.log (11631253111 / 7812500000) = -Real.log (7812500000 / 11631253111) := by
    rw [show ((11631253111 / 7812500000) : ℝ) = ((7812500000 / 11631253111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6479_neg : (199089361 / 500000000) ≤ -Real.log (250000000000 / 372277535781) ∧
    -Real.log (250000000000 / 372277535781) ≤ (398178723 / 1000000000) := by
  have h := checkLog_sound (w := (122277535781 / 622277535781)) (n := 12)
    (lo := (199089361 / 500000000)) (hi := (398178723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372277535781 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372277535781 / 250000000000) = 1/(250000000000 / 372277535781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6479 : Bounds (199089361 / 500000000) (398178723 / 1000000000) (Real.log (372277535781 / 250000000000)) := by
  have h := reflection_log_6479_neg
  have he : Real.log (372277535781 / 250000000000) = -Real.log (250000000000 / 372277535781) := by
    rw [show ((372277535781 / 250000000000) : ℝ) = ((250000000000 / 372277535781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6480_neg : (179484201 / 1000000000) ≤ -Real.log (5000 / 5983) ∧
    -Real.log (5000 / 5983) ≤ (89742101 / 500000000) := by
  have h := checkLog_sound (w := (983 / 10983)) (n := 12)
    (lo := (179484201 / 1000000000)) (hi := (89742101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5983 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5983 / 5000) = 1/(5000 / 5983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6480 : Bounds (179484201 / 1000000000) (89742101 / 500000000) (Real.log (5983 / 5000)) := by
  have h := reflection_log_6480_neg
  have he : Real.log (5983 / 5000) = -Real.log (5000 / 5983) := by
    rw [show ((5983 / 5000) : ℝ) = ((5000 / 5983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6481_neg : (218902557 / 1000000000) ≤ -Real.log (4017 / 5000) ∧
    -Real.log (4017 / 5000) ≤ (109451279 / 500000000) := by
  have h := checkLog_sound (w := (983 / 9017)) (n := 12)
    (lo := (218902557 / 1000000000)) (hi := (109451279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4017) = 1/(4017 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6481 : Bounds (-109451279 / 500000000) (-218902557 / 1000000000) (Real.log (4017 / 5000)) := by
  have h := reflection_log_6481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6482_neg : (9829 / 50000000) ≤ -Real.log (5000000 / 5000983) ∧
    -Real.log (5000000 / 5000983) ≤ (196581 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 10000983)) (n := 12)
    (lo := (9829 / 50000000)) (hi := (196581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000983 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000983 / 5000000) = 1/(5000000 / 5000983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6482 : Bounds (9829 / 50000000) (196581 / 1000000000) (Real.log (5000983 / 5000000)) := by
  have h := reflection_log_6482_neg
  have he : Real.log (5000983 / 5000000) = -Real.log (5000000 / 5000983) := by
    rw [show ((5000983 / 5000000) : ℝ) = ((5000000 / 5000983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6483_neg : (196619 / 1000000000) ≤ -Real.log (4999017 / 5000000) ∧
    -Real.log (4999017 / 5000000) ≤ (9831 / 50000000) := by
  have h := checkLog_sound (w := (983 / 9999017)) (n := 12)
    (lo := (196619 / 1000000000)) (hi := (9831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999017) = 1/(4999017 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6483 : Bounds (-9831 / 50000000) (-196619 / 1000000000) (Real.log (4999017 / 5000000)) := by
  have h := reflection_log_6483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6484_neg : (47129359 / 500000000) ≤ -Real.log (250000 / 274711) ∧
    -Real.log (250000 / 274711) ≤ (94258719 / 1000000000) := by
  have h := checkLog_sound (w := (24711 / 524711)) (n := 12)
    (lo := (47129359 / 500000000)) (hi := (94258719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274711 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274711 / 250000) = 1/(250000 / 274711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6484 : Bounds (47129359 / 500000000) (94258719 / 1000000000) (Real.log (274711 / 250000)) := by
  have h := reflection_log_6484_neg
  have he : Real.log (274711 / 250000) = -Real.log (250000 / 274711) := by
    rw [show ((274711 / 250000) : ℝ) = ((250000 / 274711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6485_neg : (20815379 / 200000000) ≤ -Real.log (225289 / 250000) ∧
    -Real.log (225289 / 250000) ≤ (3252403 / 31250000) := by
  have h := checkLog_sound (w := (24711 / 475289)) (n := 12)
    (lo := (20815379 / 200000000)) (hi := (3252403 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225289) = 1/(225289 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6485 : Bounds (-3252403 / 31250000) (-20815379 / 200000000) (Real.log (225289 / 250000)) := by
  have h := reflection_log_6485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6486_neg : (47241737 / 500000000) ≤ -Real.log (1000000 / 1099091) ∧
    -Real.log (1000000 / 1099091) ≤ (3779339 / 40000000) := by
  have h := checkLog_sound (w := (99091 / 2099091)) (n := 12)
    (lo := (47241737 / 500000000)) (hi := (3779339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099091 / 1000000) = 1/(1000000 / 1099091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6486 : Bounds (47241737 / 500000000) (3779339 / 40000000) (Real.log (1099091 / 1000000)) := by
  have h := reflection_log_6486_neg
  have he : Real.log (1099091 / 1000000) = -Real.log (1000000 / 1099091) := by
    rw [show ((1099091 / 1000000) : ℝ) = ((1000000 / 1099091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6487_neg : (4174041 / 40000000) ≤ -Real.log (900909 / 1000000) ∧
    -Real.log (900909 / 1000000) ≤ (52175513 / 500000000) := by
  have h := checkLog_sound (w := (99091 / 1900909)) (n := 12)
    (lo := (4174041 / 40000000)) (hi := (52175513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900909) = 1/(900909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6487 : Bounds (-52175513 / 500000000) (-4174041 / 40000000) (Real.log (900909 / 1000000)) := by
  have h := reflection_log_6487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6488_neg : (197351 / 20000000) ≤ -Real.log (990180973719 / 1000000000000) ∧
    -Real.log (990180973719 / 1000000000000) ≤ (9867551 / 1000000000) := by
  have h := checkLog_sound (w := (9819026281 / 1990180973719)) (n := 12)
    (lo := (197351 / 20000000)) (hi := (9867551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990180973719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990180973719) = 1/(990180973719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6488 : Bounds (-9867551 / 1000000000) (-197351 / 20000000) (Real.log (990180973719 / 1000000000000)) := by
  have h := reflection_log_6488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6489_neg : (9818177 / 1000000000) ≤ -Real.log (61889366479 / 62500000000) ∧
    -Real.log (61889366479 / 62500000000) ≤ (4909089 / 500000000) := by
  have h := checkLog_sound (w := (610633521 / 124389366479)) (n := 12)
    (lo := (9818177 / 1000000000)) (hi := (4909089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61889366479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61889366479) = 1/(61889366479 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6489 : Bounds (-4909089 / 500000000) (-9818177 / 1000000000) (Real.log (61889366479 / 62500000000)) := by
  have h := reflection_log_6489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6490_neg : (198335613 / 1000000000) ≤ -Real.log (250000000000 / 304842890687) ∧
    -Real.log (250000000000 / 304842890687) ≤ (99167807 / 500000000) := by
  have h := checkLog_sound (w := (54842890687 / 554842890687)) (n := 12)
    (lo := (198335613 / 1000000000)) (hi := (99167807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304842890687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304842890687 / 250000000000) = 1/(250000000000 / 304842890687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6490 : Bounds (198335613 / 1000000000) (99167807 / 500000000) (Real.log (304842890687 / 250000000000)) := by
  have h := reflection_log_6490_neg
  have he : Real.log (304842890687 / 250000000000) = -Real.log (250000000000 / 304842890687) := by
    rw [show ((304842890687 / 250000000000) : ℝ) = ((250000000000 / 304842890687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6491_neg : (198834499 / 1000000000) ≤ -Real.log (50000000000 / 60999002119) ∧
    -Real.log (50000000000 / 60999002119) ≤ (397669 / 2000000) := by
  have h := checkLog_sound (w := (10999002119 / 110999002119)) (n := 12)
    (lo := (198834499 / 1000000000)) (hi := (397669 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60999002119 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60999002119 / 50000000000) = 1/(50000000000 / 60999002119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6491 : Bounds (198834499 / 1000000000) (397669 / 2000000) (Real.log (60999002119 / 50000000000)) := by
  have h := reflection_log_6491_neg
  have he : Real.log (60999002119 / 50000000000) = -Real.log (50000000000 / 60999002119) := by
    rw [show ((60999002119 / 50000000000) : ℝ) = ((50000000000 / 60999002119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6492_neg : (199089361 / 500000000) ≤ -Real.log (500000000000 / 744555071561) ∧
    -Real.log (500000000000 / 744555071561) ≤ (398178723 / 1000000000) := by
  have h := checkLog_sound (w := (244555071561 / 1244555071561)) (n := 12)
    (lo := (199089361 / 500000000)) (hi := (398178723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744555071561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744555071561 / 500000000000) = 1/(500000000000 / 744555071561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6492 : Bounds (199089361 / 500000000) (398178723 / 1000000000) (Real.log (744555071561 / 500000000000)) := by
  have h := reflection_log_6492_neg
  have he : Real.log (744555071561 / 500000000000) = -Real.log (500000000000 / 744555071561) := by
    rw [show ((744555071561 / 500000000000) : ℝ) = ((500000000000 / 744555071561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6493_neg : (398386759 / 1000000000) ≤ -Real.log (20000000000 / 29788399303) ∧
    -Real.log (20000000000 / 29788399303) ≤ (9959669 / 25000000) := by
  have h := checkLog_sound (w := (9788399303 / 49788399303)) (n := 12)
    (lo := (398386759 / 1000000000)) (hi := (9959669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29788399303 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29788399303 / 20000000000) = 1/(20000000000 / 29788399303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6493 : Bounds (398386759 / 1000000000) (9959669 / 25000000) (Real.log (29788399303 / 20000000000)) := by
  have h := reflection_log_6493_neg
  have he : Real.log (29788399303 / 20000000000) = -Real.log (20000000000 / 29788399303) := by
    rw [show ((29788399303 / 20000000000) : ℝ) = ((20000000000 / 29788399303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6494_neg : (22445971 / 125000000) ≤ -Real.log (10000 / 11967) ∧
    -Real.log (10000 / 11967) ≤ (179567769 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 21967)) (n := 12)
    (lo := (22445971 / 125000000)) (hi := (179567769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11967 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11967 / 10000) = 1/(10000 / 11967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6494 : Bounds (22445971 / 125000000) (179567769 / 1000000000) (Real.log (11967 / 10000)) := by
  have h := reflection_log_6494_neg
  have he : Real.log (11967 / 10000) = -Real.log (10000 / 11967) := by
    rw [show ((11967 / 10000) : ℝ) = ((10000 / 11967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6495_neg : (43805407 / 200000000) ≤ -Real.log (8033 / 10000) ∧
    -Real.log (8033 / 10000) ≤ (54756759 / 250000000) := by
  have h := checkLog_sound (w := (1967 / 18033)) (n := 12)
    (lo := (43805407 / 200000000)) (hi := (54756759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8033) = 1/(8033 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6495 : Bounds (-54756759 / 250000000) (-43805407 / 200000000) (Real.log (8033 / 10000)) := by
  have h := reflection_log_6495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6496_neg : (4917 / 25000000) ≤ -Real.log (10000000 / 10001967) ∧
    -Real.log (10000000 / 10001967) ≤ (196681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 20001967)) (n := 12)
    (lo := (4917 / 25000000)) (hi := (196681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001967 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001967 / 10000000) = 1/(10000000 / 10001967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6496 : Bounds (4917 / 25000000) (196681 / 1000000000) (Real.log (10001967 / 10000000)) := by
  have h := reflection_log_6496_neg
  have he : Real.log (10001967 / 10000000) = -Real.log (10000000 / 10001967) := by
    rw [show ((10001967 / 10000000) : ℝ) = ((10000000 / 10001967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6497_neg : (196719 / 1000000000) ≤ -Real.log (9998033 / 10000000) ∧
    -Real.log (9998033 / 10000000) ≤ (2459 / 12500000) := by
  have h := checkLog_sound (w := (1967 / 19998033)) (n := 12)
    (lo := (196719 / 1000000000)) (hi := (2459 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998033) = 1/(9998033 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6497 : Bounds (-2459 / 12500000) (-196719 / 1000000000) (Real.log (9998033 / 10000000)) := by
  have h := reflection_log_6497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6498_neg : (94305129 / 1000000000) ≤ -Real.log (200000 / 219779) ∧
    -Real.log (200000 / 219779) ≤ (9430513 / 100000000) := by
  have h := checkLog_sound (w := (19779 / 419779)) (n := 12)
    (lo := (94305129 / 1000000000)) (hi := (9430513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219779 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219779 / 200000) = 1/(200000 / 219779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6498 : Bounds (94305129 / 1000000000) (9430513 / 100000000) (Real.log (219779 / 200000)) := by
  have h := reflection_log_6498_neg
  have he : Real.log (219779 / 200000) = -Real.log (200000 / 219779) := by
    rw [show ((219779 / 200000) : ℝ) = ((200000 / 219779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6499_neg : (10413349 / 100000000) ≤ -Real.log (180221 / 200000) ∧
    -Real.log (180221 / 200000) ≤ (104133491 / 1000000000) := by
  have h := checkLog_sound (w := (19779 / 380221)) (n := 12)
    (lo := (10413349 / 100000000)) (hi := (104133491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180221) = 1/(180221 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6499 : Bounds (-104133491 / 1000000000) (-10413349 / 100000000) (Real.log (180221 / 200000)) := by
  have h := reflection_log_6499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6500_neg : (756239 / 8000000) ≤ -Real.log (500000 / 549571) ∧
    -Real.log (500000 / 549571) ≤ (23632469 / 250000000) := by
  have h := checkLog_sound (w := (49571 / 1049571)) (n := 12)
    (lo := (756239 / 8000000)) (hi := (23632469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549571 / 500000) = 1/(500000 / 549571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6500 : Bounds (756239 / 8000000) (23632469 / 250000000) (Real.log (549571 / 500000)) := by
  have h := reflection_log_6500_neg
  have he : Real.log (549571 / 500000) = -Real.log (500000 / 549571) := by
    rw [show ((549571 / 500000) : ℝ) = ((500000 / 549571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6501_neg : (26101909 / 250000000) ≤ -Real.log (450429 / 500000) ∧
    -Real.log (450429 / 500000) ≤ (104407637 / 1000000000) := by
  have h := checkLog_sound (w := (49571 / 950429)) (n := 12)
    (lo := (26101909 / 250000000)) (hi := (104407637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450429) = 1/(450429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6501 : Bounds (-104407637 / 1000000000) (-26101909 / 250000000) (Real.log (450429 / 500000)) := by
  have h := reflection_log_6501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6502_neg : (9877761 / 1000000000) ≤ -Real.log (247542715959 / 250000000000) ∧
    -Real.log (247542715959 / 250000000000) ≤ (4938881 / 500000000) := by
  have h := checkLog_sound (w := (2457284041 / 497542715959)) (n := 12)
    (lo := (9877761 / 1000000000)) (hi := (4938881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247542715959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247542715959) = 1/(247542715959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6502 : Bounds (-4938881 / 500000000) (-9877761 / 1000000000) (Real.log (247542715959 / 250000000000)) := by
  have h := reflection_log_6502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6503_neg : (9828361 / 1000000000) ≤ -Real.log (39608791159 / 40000000000) ∧
    -Real.log (39608791159 / 40000000000) ≤ (4914181 / 500000000) := by
  have h := checkLog_sound (w := (391208841 / 79608791159)) (n := 12)
    (lo := (9828361 / 1000000000)) (hi := (4914181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39608791159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39608791159) = 1/(39608791159 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6503 : Bounds (-4914181 / 500000000) (-9828361 / 1000000000) (Real.log (39608791159 / 40000000000)) := by
  have h := reflection_log_6503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6504_neg : (9921931 / 50000000) ≤ -Real.log (500000000000 / 609748586457) ∧
    -Real.log (500000000000 / 609748586457) ≤ (198438621 / 1000000000) := by
  have h := checkLog_sound (w := (109748586457 / 1109748586457)) (n := 12)
    (lo := (9921931 / 50000000)) (hi := (198438621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609748586457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609748586457 / 500000000000) = 1/(500000000000 / 609748586457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6504 : Bounds (9921931 / 50000000) (198438621 / 1000000000) (Real.log (609748586457 / 500000000000)) := by
  have h := reflection_log_6504_neg
  have he : Real.log (609748586457 / 500000000000) = -Real.log (500000000000 / 609748586457) := by
    rw [show ((609748586457 / 500000000000) : ℝ) = ((500000000000 / 609748586457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6505_neg : (198937511 / 1000000000) ≤ -Real.log (250000000000 / 305026430359) ∧
    -Real.log (250000000000 / 305026430359) ≤ (24867189 / 125000000) := by
  have h := checkLog_sound (w := (55026430359 / 555026430359)) (n := 12)
    (lo := (198937511 / 1000000000)) (hi := (24867189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305026430359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305026430359 / 250000000000) = 1/(250000000000 / 305026430359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6505 : Bounds (198937511 / 1000000000) (24867189 / 125000000) (Real.log (305026430359 / 250000000000)) := by
  have h := reflection_log_6505_neg
  have he : Real.log (305026430359 / 250000000000) = -Real.log (250000000000 / 305026430359) := by
    rw [show ((305026430359 / 250000000000) : ℝ) = ((250000000000 / 305026430359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6506_neg : (398386759 / 1000000000) ≤ -Real.log (250000000000 / 372354991287) ∧
    -Real.log (250000000000 / 372354991287) ≤ (9959669 / 25000000) := by
  have h := checkLog_sound (w := (122354991287 / 622354991287)) (n := 12)
    (lo := (398386759 / 1000000000)) (hi := (9959669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372354991287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372354991287 / 250000000000) = 1/(250000000000 / 372354991287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6506 : Bounds (398386759 / 1000000000) (9959669 / 25000000) (Real.log (372354991287 / 250000000000)) := by
  have h := reflection_log_6506_neg
  have he : Real.log (372354991287 / 250000000000) = -Real.log (250000000000 / 372354991287) := by
    rw [show ((372354991287 / 250000000000) : ℝ) = ((250000000000 / 372354991287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6507_neg : (99648701 / 250000000) ≤ -Real.log (100000000000 / 148972986431) ∧
    -Real.log (100000000000 / 148972986431) ≤ (79718961 / 200000000) := by
  have h := checkLog_sound (w := (48972986431 / 248972986431)) (n := 12)
    (lo := (99648701 / 250000000)) (hi := (79718961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148972986431 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148972986431 / 100000000000) = 1/(100000000000 / 148972986431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6507 : Bounds (99648701 / 250000000) (79718961 / 200000000) (Real.log (148972986431 / 100000000000)) := by
  have h := reflection_log_6507_neg
  have he : Real.log (148972986431 / 100000000000) = -Real.log (100000000000 / 148972986431) := by
    rw [show ((148972986431 / 100000000000) : ℝ) = ((100000000000 / 148972986431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6508_neg : (701763 / 3906250) ≤ -Real.log (625 / 748) ∧
    -Real.log (625 / 748) ≤ (179651329 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1373)) (n := 12)
    (lo := (701763 / 3906250)) (hi := (179651329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748 / 625) = 1/(625 / 748) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6508 : Bounds (701763 / 3906250) (179651329 / 1000000000) (Real.log (748 / 625)) := by
  have h := reflection_log_6508_neg
  have he : Real.log (748 / 625) = -Real.log (625 / 748) := by
    rw [show ((748 / 625) : ℝ) = ((625 / 748) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6509_neg : (21915153 / 100000000) ≤ -Real.log (502 / 625) ∧
    -Real.log (502 / 625) ≤ (219151531 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1127)) (n := 12)
    (lo := (21915153 / 100000000)) (hi := (219151531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 502) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 502) = 1/(502 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6509 : Bounds (-219151531 / 1000000000) (-21915153 / 100000000) (Real.log (502 / 625)) := by
  have h := reflection_log_6509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6510_neg : (9839 / 50000000) ≤ -Real.log (625000 / 625123) ∧
    -Real.log (625000 / 625123) ≤ (196781 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1250123)) (n := 12)
    (lo := (9839 / 50000000)) (hi := (196781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625123 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625123 / 625000) = 1/(625000 / 625123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6510 : Bounds (9839 / 50000000) (196781 / 1000000000) (Real.log (625123 / 625000)) := by
  have h := reflection_log_6510_neg
  have he : Real.log (625123 / 625000) = -Real.log (625000 / 625123) := by
    rw [show ((625123 / 625000) : ℝ) = ((625000 / 625123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6511_neg : (196819 / 1000000000) ≤ -Real.log (624877 / 625000) ∧
    -Real.log (624877 / 625000) ≤ (9841 / 50000000) := by
  have h := checkLog_sound (w := (123 / 1249877)) (n := 12)
    (lo := (196819 / 1000000000)) (hi := (9841 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624877) = 1/(624877 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6511 : Bounds (-9841 / 50000000) (-196819 / 1000000000) (Real.log (624877 / 625000)) := by
  have h := reflection_log_6511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6512_neg : (47175769 / 500000000) ≤ -Real.log (500000 / 549473) ∧
    -Real.log (500000 / 549473) ≤ (94351539 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 1049473)) (n := 12)
    (lo := (47175769 / 500000000)) (hi := (94351539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549473 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549473 / 500000) = 1/(500000 / 549473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6512 : Bounds (47175769 / 500000000) (94351539 / 1000000000) (Real.log (549473 / 500000)) := by
  have h := reflection_log_6512_neg
  have he : Real.log (549473 / 500000) = -Real.log (500000 / 549473) := by
    rw [show ((549473 / 500000) : ℝ) = ((500000 / 549473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6513_neg : (104190089 / 1000000000) ≤ -Real.log (450527 / 500000) ∧
    -Real.log (450527 / 500000) ≤ (10419009 / 100000000) := by
  have h := checkLog_sound (w := (49473 / 950527)) (n := 12)
    (lo := (104190089 / 1000000000)) (hi := (10419009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450527) = 1/(450527 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6513 : Bounds (-10419009 / 100000000) (-104190089 / 1000000000) (Real.log (450527 / 500000)) := by
  have h := reflection_log_6513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6514_neg : (47288137 / 500000000) ≤ -Real.log (1000000 / 1099193) ∧
    -Real.log (1000000 / 1099193) ≤ (3783051 / 40000000) := by
  have h := checkLog_sound (w := (99193 / 2099193)) (n := 12)
    (lo := (47288137 / 500000000)) (hi := (3783051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099193 / 1000000) = 1/(1000000 / 1099193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6514 : Bounds (47288137 / 500000000) (3783051 / 40000000) (Real.log (1099193 / 1000000)) := by
  have h := reflection_log_6514_neg
  have he : Real.log (1099193 / 1000000) = -Real.log (1000000 / 1099193) := by
    rw [show ((1099193 / 1000000) : ℝ) = ((1000000 / 1099193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6515_neg : (417857 / 4000000) ≤ -Real.log (900807 / 1000000) ∧
    -Real.log (900807 / 1000000) ≤ (104464251 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 1900807)) (n := 12)
    (lo := (417857 / 4000000)) (hi := (104464251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900807) = 1/(900807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6515 : Bounds (-104464251 / 1000000000) (-417857 / 4000000) (Real.log (900807 / 1000000)) := by
  have h := reflection_log_6515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6516_neg : (1235997 / 125000000) ≤ -Real.log (990160748751 / 1000000000000) ∧
    -Real.log (990160748751 / 1000000000000) ≤ (9887977 / 1000000000) := by
  have h := checkLog_sound (w := (9839251249 / 1990160748751)) (n := 12)
    (lo := (1235997 / 125000000)) (hi := (9887977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990160748751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990160748751) = 1/(990160748751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6516 : Bounds (-9887977 / 1000000000) (-1235997 / 125000000) (Real.log (990160748751 / 1000000000000)) := by
  have h := reflection_log_6516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6517_neg : (9838551 / 1000000000) ≤ -Real.log (247552422271 / 250000000000) ∧
    -Real.log (247552422271 / 250000000000) ≤ (1229819 / 125000000) := by
  have h := checkLog_sound (w := (2447577729 / 497552422271)) (n := 12)
    (lo := (9838551 / 1000000000)) (hi := (1229819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247552422271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247552422271) = 1/(247552422271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6517 : Bounds (-1229819 / 125000000) (-9838551 / 1000000000) (Real.log (247552422271 / 250000000000)) := by
  have h := reflection_log_6517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6518_neg : (49635407 / 250000000) ≤ -Real.log (10000000000 / 12196227973) ∧
    -Real.log (10000000000 / 12196227973) ≤ (198541629 / 1000000000) := by
  have h := checkLog_sound (w := (2196227973 / 22196227973)) (n := 12)
    (lo := (49635407 / 250000000)) (hi := (198541629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12196227973 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12196227973 / 10000000000) = 1/(10000000000 / 12196227973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6518 : Bounds (49635407 / 250000000) (198541629 / 1000000000) (Real.log (12196227973 / 10000000000)) := by
  have h := reflection_log_6518_neg
  have he : Real.log (12196227973 / 10000000000) = -Real.log (10000000000 / 12196227973) := by
    rw [show ((12196227973 / 10000000000) : ℝ) = ((10000000000 / 12196227973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6519_neg : (49760131 / 250000000) ≤ -Real.log (500000000000 / 610115707361) ∧
    -Real.log (500000000000 / 610115707361) ≤ (7961621 / 40000000) := by
  have h := checkLog_sound (w := (110115707361 / 1110115707361)) (n := 12)
    (lo := (49760131 / 250000000)) (hi := (7961621 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610115707361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610115707361 / 500000000000) = 1/(500000000000 / 610115707361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6519 : Bounds (49760131 / 250000000) (7961621 / 40000000) (Real.log (610115707361 / 500000000000)) := by
  have h := reflection_log_6519_neg
  have he : Real.log (610115707361 / 500000000000) = -Real.log (500000000000 / 610115707361) := by
    rw [show ((610115707361 / 500000000000) : ℝ) = ((500000000000 / 610115707361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6520_neg : (99648701 / 250000000) ≤ -Real.log (250000000000 / 372432466077) ∧
    -Real.log (250000000000 / 372432466077) ≤ (79718961 / 200000000) := by
  have h := checkLog_sound (w := (122432466077 / 622432466077)) (n := 12)
    (lo := (99648701 / 250000000)) (hi := (79718961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372432466077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372432466077 / 250000000000) = 1/(250000000000 / 372432466077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6520 : Bounds (99648701 / 250000000) (79718961 / 200000000) (Real.log (372432466077 / 250000000000)) := by
  have h := reflection_log_6520_neg
  have he : Real.log (372432466077 / 250000000000) = -Real.log (250000000000 / 372432466077) := by
    rw [show ((372432466077 / 250000000000) : ℝ) = ((250000000000 / 372432466077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6521_neg : (199401429 / 500000000) ≤ -Real.log (500000000000 / 745019920319) ∧
    -Real.log (500000000000 / 745019920319) ≤ (398802859 / 1000000000) := by
  have h := checkLog_sound (w := (245019920319 / 1245019920319)) (n := 12)
    (lo := (199401429 / 500000000)) (hi := (398802859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745019920319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745019920319 / 500000000000) = 1/(500000000000 / 745019920319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6521 : Bounds (199401429 / 500000000) (398802859 / 1000000000) (Real.log (745019920319 / 500000000000)) := by
  have h := reflection_log_6521_neg
  have he : Real.log (745019920319 / 500000000000) = -Real.log (500000000000 / 745019920319) := by
    rw [show ((745019920319 / 500000000000) : ℝ) = ((500000000000 / 745019920319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6522_neg : (1123343 / 6250000) ≤ -Real.log (10000 / 11969) ∧
    -Real.log (10000 / 11969) ≤ (179734881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 21969)) (n := 12)
    (lo := (1123343 / 6250000)) (hi := (179734881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 10000) = 1/(10000 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6522 : Bounds (1123343 / 6250000) (179734881 / 1000000000) (Real.log (11969 / 10000)) := by
  have h := reflection_log_6522_neg
  have he : Real.log (11969 / 10000) = -Real.log (10000 / 11969) := by
    rw [show ((11969 / 10000) : ℝ) = ((10000 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6523_neg : (219276039 / 1000000000) ≤ -Real.log (8031 / 10000) ∧
    -Real.log (8031 / 10000) ≤ (5481901 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 18031)) (n := 12)
    (lo := (219276039 / 1000000000)) (hi := (5481901 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8031) = 1/(8031 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6523 : Bounds (-5481901 / 25000000) (-219276039 / 1000000000) (Real.log (8031 / 10000)) := by
  have h := reflection_log_6523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6524_neg : (2461 / 12500000) ≤ -Real.log (10000000 / 10001969) ∧
    -Real.log (10000000 / 10001969) ≤ (196881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 20001969)) (n := 12)
    (lo := (2461 / 12500000)) (hi := (196881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001969 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001969 / 10000000) = 1/(10000000 / 10001969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6524 : Bounds (2461 / 12500000) (196881 / 1000000000) (Real.log (10001969 / 10000000)) := by
  have h := reflection_log_6524_neg
  have he : Real.log (10001969 / 10000000) = -Real.log (10000000 / 10001969) := by
    rw [show ((10001969 / 10000000) : ℝ) = ((10000000 / 10001969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6525_neg : (196919 / 1000000000) ≤ -Real.log (9998031 / 10000000) ∧
    -Real.log (9998031 / 10000000) ≤ (4923 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 19998031)) (n := 12)
    (lo := (196919 / 1000000000)) (hi := (4923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998031) = 1/(9998031 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6525 : Bounds (-4923 / 25000000) (-196919 / 1000000000) (Real.log (9998031 / 10000000)) := by
  have h := reflection_log_6525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6526_neg : (18879589 / 200000000) ≤ -Real.log (1000000 / 1098997) ∧
    -Real.log (1000000 / 1098997) ≤ (47198973 / 500000000) := by
  have h := checkLog_sound (w := (98997 / 2098997)) (n := 12)
    (lo := (18879589 / 200000000)) (hi := (47198973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098997 / 1000000) = 1/(1000000 / 1098997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6526 : Bounds (18879589 / 200000000) (47198973 / 500000000) (Real.log (1098997 / 1000000)) := by
  have h := reflection_log_6526_neg
  have he : Real.log (1098997 / 1000000) = -Real.log (1000000 / 1098997) := by
    rw [show ((1098997 / 1000000) : ℝ) = ((1000000 / 1098997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6527_neg : (104246691 / 1000000000) ≤ -Real.log (901003 / 1000000) ∧
    -Real.log (901003 / 1000000) ≤ (26061673 / 250000000) := by
  have h := checkLog_sound (w := (98997 / 1901003)) (n := 12)
    (lo := (104246691 / 1000000000)) (hi := (26061673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901003) = 1/(901003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6527 : Bounds (-26061673 / 250000000) (-104246691 / 1000000000) (Real.log (901003 / 1000000)) := by
  have h := reflection_log_6527_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


