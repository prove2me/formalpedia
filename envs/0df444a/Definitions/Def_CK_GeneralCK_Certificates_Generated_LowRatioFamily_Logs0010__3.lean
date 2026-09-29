-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0010__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0010__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:56:10.175793+00:00
-- url     : https://prove2.me/theorems/06214732-c0bd-4078-b9a1-1aef07d3ce81
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0010 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0011, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0010 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0011, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0012)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0010 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0011, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0012)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0010 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0011, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0012) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0010 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0011, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0012).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0010 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_640_neg : (19492907 / 125000000) ≤ -Real.log (500000000000 / 584379940707) ∧
    -Real.log (500000000000 / 584379940707) ≤ (155943257 / 1000000000) := by
  have h := checkLog_sound (w := (84379940707 / 1084379940707)) (n := 12)
    (lo := (19492907 / 125000000)) (hi := (155943257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584379940707 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584379940707 / 500000000000) = 1/(500000000000 / 584379940707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_640 : Bounds (19492907 / 125000000) (155943257 / 1000000000) (Real.log (584379940707 / 500000000000)) := by
  have h := reflection_log_640_neg
  have he : Real.log (584379940707 / 500000000000) = -Real.log (500000000000 / 584379940707) := by
    rw [show ((584379940707 / 500000000000) : ℝ) = ((500000000000 / 584379940707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_641_neg : (62380851 / 200000000) ≤ -Real.log (25000000000 / 34150597421) ∧
    -Real.log (25000000000 / 34150597421) ≤ (609188 / 1953125) := by
  have h := checkLog_sound (w := (9150597421 / 59150597421)) (n := 12)
    (lo := (62380851 / 200000000)) (hi := (609188 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34150597421 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34150597421 / 25000000000) = 1/(25000000000 / 34150597421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_641 : Bounds (62380851 / 200000000) (609188 / 1953125) (Real.log (34150597421 / 25000000000)) := by
  have h := reflection_log_641_neg
  have he : Real.log (34150597421 / 25000000000) = -Real.log (25000000000 / 34150597421) := by
    rw [show ((34150597421 / 25000000000) : ℝ) = ((25000000000 / 34150597421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_642_neg : (156054581 / 500000000) ≤ -Real.log (500000000000 / 683151916707) ∧
    -Real.log (500000000000 / 683151916707) ≤ (312109163 / 1000000000) := by
  have h := checkLog_sound (w := (183151916707 / 1183151916707)) (n := 12)
    (lo := (156054581 / 500000000)) (hi := (312109163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683151916707 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683151916707 / 500000000000) = 1/(500000000000 / 683151916707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_642 : Bounds (156054581 / 500000000) (312109163 / 1000000000) (Real.log (683151916707 / 500000000000)) := by
  have h := reflection_log_642_neg
  have he : Real.log (683151916707 / 500000000000) = -Real.log (500000000000 / 683151916707) := by
    rw [show ((683151916707 / 500000000000) : ℝ) = ((500000000000 / 683151916707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_643_neg : (450043 / 3125000) ≤ -Real.log (10000 / 11549) ∧
    -Real.log (10000 / 11549) ≤ (144013761 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 21549)) (n := 12)
    (lo := (450043 / 3125000)) (hi := (144013761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11549 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11549 / 10000) = 1/(10000 / 11549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_643 : Bounds (450043 / 3125000) (144013761 / 1000000000) (Real.log (11549 / 10000)) := by
  have h := reflection_log_643_neg
  have he : Real.log (11549 / 10000) = -Real.log (10000 / 11549) := by
    rw [show ((11549 / 10000) : ℝ) = ((10000 / 11549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_644_neg : (33660063 / 200000000) ≤ -Real.log (8451 / 10000) ∧
    -Real.log (8451 / 10000) ≤ (42075079 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 18451)) (n := 12)
    (lo := (33660063 / 200000000)) (hi := (42075079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8451) = 1/(8451 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_644 : Bounds (-42075079 / 250000000) (-33660063 / 200000000) (Real.log (8451 / 10000)) := by
  have h := reflection_log_644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_645_neg : (19361 / 125000000) ≤ -Real.log (10000000 / 10001549) ∧
    -Real.log (10000000 / 10001549) ≤ (154889 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 20001549)) (n := 12)
    (lo := (19361 / 125000000)) (hi := (154889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001549 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001549 / 10000000) = 1/(10000000 / 10001549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_645 : Bounds (19361 / 125000000) (154889 / 1000000000) (Real.log (10001549 / 10000000)) := by
  have h := reflection_log_645_neg
  have he : Real.log (10001549 / 10000000) = -Real.log (10000000 / 10001549) := by
    rw [show ((10001549 / 10000000) : ℝ) = ((10000000 / 10001549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_646_neg : (154911 / 1000000000) ≤ -Real.log (9998451 / 10000000) ∧
    -Real.log (9998451 / 10000000) ≤ (4841 / 31250000) := by
  have h := checkLog_sound (w := (1549 / 19998451)) (n := 12)
    (lo := (154911 / 1000000000)) (hi := (4841 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998451) = 1/(9998451 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_646 : Bounds (-4841 / 31250000) (-154911 / 1000000000) (Real.log (9998451 / 10000000)) := by
  have h := reflection_log_646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_647_neg : (14958219 / 200000000) ≤ -Real.log (1000000 / 1077659) ∧
    -Real.log (1000000 / 1077659) ≤ (9348887 / 125000000) := by
  have h := checkLog_sound (w := (77659 / 2077659)) (n := 12)
    (lo := (14958219 / 200000000)) (hi := (9348887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077659 / 1000000) = 1/(1000000 / 1077659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_647 : Bounds (14958219 / 200000000) (9348887 / 125000000) (Real.log (1077659 / 1000000)) := by
  have h := reflection_log_647_neg
  have he : Real.log (1077659 / 1000000) = -Real.log (1000000 / 1077659) := by
    rw [show ((1077659 / 1000000) : ℝ) = ((1000000 / 1077659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_648_neg : (3233611 / 40000000) ≤ -Real.log (922341 / 1000000) ∧
    -Real.log (922341 / 1000000) ≤ (20210069 / 250000000) := by
  have h := checkLog_sound (w := (77659 / 1922341)) (n := 12)
    (lo := (3233611 / 40000000)) (hi := (20210069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922341) = 1/(922341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_648 : Bounds (-20210069 / 250000000) (-3233611 / 40000000) (Real.log (922341 / 1000000)) := by
  have h := reflection_log_648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_649_neg : (9372779 / 125000000) ≤ -Real.log (200000 / 215573) ∧
    -Real.log (200000 / 215573) ≤ (74982233 / 1000000000) := by
  have h := checkLog_sound (w := (15573 / 415573)) (n := 12)
    (lo := (9372779 / 125000000)) (hi := (74982233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215573 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215573 / 200000) = 1/(200000 / 215573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_649 : Bounds (9372779 / 125000000) (74982233 / 1000000000) (Real.log (215573 / 200000)) := by
  have h := reflection_log_649_neg
  have he : Real.log (215573 / 200000) = -Real.log (200000 / 215573) := by
    rw [show ((215573 / 200000) : ℝ) = ((200000 / 215573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_650_neg : (16212729 / 200000000) ≤ -Real.log (184427 / 200000) ∧
    -Real.log (184427 / 200000) ≤ (40531823 / 500000000) := by
  have h := checkLog_sound (w := (15573 / 384427)) (n := 12)
    (lo := (16212729 / 200000000)) (hi := (40531823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184427) = 1/(184427 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_650 : Bounds (-40531823 / 500000000) (-16212729 / 200000000) (Real.log (184427 / 200000)) := by
  have h := reflection_log_650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_651_neg : (1520353 / 250000000) ≤ -Real.log (39757481671 / 40000000000) ∧
    -Real.log (39757481671 / 40000000000) ≤ (6081413 / 1000000000) := by
  have h := checkLog_sound (w := (242518329 / 79757481671)) (n := 12)
    (lo := (1520353 / 250000000)) (hi := (6081413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39757481671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39757481671) = 1/(39757481671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_651 : Bounds (-6081413 / 1000000000) (-1520353 / 250000000) (Real.log (39757481671 / 40000000000)) := by
  have h := reflection_log_651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_652_neg : (6049179 / 1000000000) ≤ -Real.log (993969079719 / 1000000000000) ∧
    -Real.log (993969079719 / 1000000000000) ≤ (302459 / 50000000) := by
  have h := checkLog_sound (w := (6030920281 / 1993969079719)) (n := 12)
    (lo := (6049179 / 1000000000)) (hi := (302459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993969079719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993969079719) = 1/(993969079719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_652 : Bounds (-302459 / 50000000) (-6049179 / 1000000000) (Real.log (993969079719 / 1000000000000)) := by
  have h := reflection_log_652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_653_neg : (155631371 / 1000000000) ≤ -Real.log (500000000000 / 584197709957) ∧
    -Real.log (500000000000 / 584197709957) ≤ (38907843 / 250000000) := by
  have h := checkLog_sound (w := (84197709957 / 1084197709957)) (n := 12)
    (lo := (155631371 / 1000000000)) (hi := (38907843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584197709957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584197709957 / 500000000000) = 1/(500000000000 / 584197709957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_653 : Bounds (155631371 / 1000000000) (38907843 / 250000000) (Real.log (584197709957 / 500000000000)) := by
  have h := reflection_log_653_neg
  have he : Real.log (584197709957 / 500000000000) = -Real.log (500000000000 / 584197709957) := by
    rw [show ((584197709957 / 500000000000) : ℝ) = ((500000000000 / 584197709957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_654_neg : (78022939 / 500000000) ≤ -Real.log (62500000000 / 73054989237) ∧
    -Real.log (62500000000 / 73054989237) ≤ (156045879 / 1000000000) := by
  have h := checkLog_sound (w := (10554989237 / 135554989237)) (n := 12)
    (lo := (78022939 / 500000000)) (hi := (156045879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73054989237 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73054989237 / 62500000000) = 1/(62500000000 / 73054989237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_654 : Bounds (78022939 / 500000000) (156045879 / 1000000000) (Real.log (73054989237 / 62500000000)) := by
  have h := reflection_log_654_neg
  have he : Real.log (73054989237 / 62500000000) = -Real.log (62500000000 / 73054989237) := by
    rw [show ((73054989237 / 62500000000) : ℝ) = ((62500000000 / 73054989237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_655_neg : (156054581 / 500000000) ≤ -Real.log (250000000000 / 341575958353) ∧
    -Real.log (250000000000 / 341575958353) ≤ (312109163 / 1000000000) := by
  have h := checkLog_sound (w := (91575958353 / 591575958353)) (n := 12)
    (lo := (156054581 / 500000000)) (hi := (312109163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341575958353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341575958353 / 250000000000) = 1/(250000000000 / 341575958353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_655 : Bounds (156054581 / 500000000) (312109163 / 1000000000) (Real.log (341575958353 / 250000000000)) := by
  have h := reflection_log_655_neg
  have he : Real.log (341575958353 / 250000000000) = -Real.log (250000000000 / 341575958353) := by
    rw [show ((341575958353 / 250000000000) : ℝ) = ((250000000000 / 341575958353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_656_neg : (12492563 / 40000000) ≤ -Real.log (500000000000 / 683291918117) ∧
    -Real.log (500000000000 / 683291918117) ≤ (78078519 / 250000000) := by
  have h := checkLog_sound (w := (183291918117 / 1183291918117)) (n := 12)
    (lo := (12492563 / 40000000)) (hi := (78078519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683291918117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683291918117 / 500000000000) = 1/(500000000000 / 683291918117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_656 : Bounds (12492563 / 40000000) (78078519 / 250000000) (Real.log (683291918117 / 500000000000)) := by
  have h := reflection_log_656_neg
  have he : Real.log (683291918117 / 500000000000) = -Real.log (500000000000 / 683291918117) := by
    rw [show ((683291918117 / 500000000000) : ℝ) = ((500000000000 / 683291918117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_657_neg : (144100343 / 1000000000) ≤ -Real.log (200 / 231) ∧
    -Real.log (200 / 231) ≤ (18012543 / 125000000) := by
  have h := checkLog_sound (w := (31 / 431)) (n := 12)
    (lo := (144100343 / 1000000000)) (hi := (18012543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 200) = 1/(200 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_657 : Bounds (144100343 / 1000000000) (18012543 / 125000000) (Real.log (231 / 200)) := by
  have h := reflection_log_657_neg
  have he : Real.log (231 / 200) = -Real.log (200 / 231) := by
    rw [show ((231 / 200) : ℝ) = ((200 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_658_neg : (168418651 / 1000000000) ≤ -Real.log (169 / 200) ∧
    -Real.log (169 / 200) ≤ (42104663 / 250000000) := by
  have h := checkLog_sound (w := (31 / 369)) (n := 12)
    (lo := (168418651 / 1000000000)) (hi := (42104663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 169) = 1/(169 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_658 : Bounds (-42104663 / 250000000) (-168418651 / 1000000000) (Real.log (169 / 200)) := by
  have h := reflection_log_658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_659_neg : (154987 / 1000000000) ≤ -Real.log (200000 / 200031) ∧
    -Real.log (200000 / 200031) ≤ (38747 / 250000000) := by
  have h := checkLog_sound (w := (31 / 400031)) (n := 12)
    (lo := (154987 / 1000000000)) (hi := (38747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200031 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200031 / 200000) = 1/(200000 / 200031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_659 : Bounds (154987 / 1000000000) (38747 / 250000000) (Real.log (200031 / 200000)) := by
  have h := reflection_log_659_neg
  have he : Real.log (200031 / 200000) = -Real.log (200000 / 200031) := by
    rw [show ((200031 / 200000) : ℝ) = ((200000 / 200031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_660_neg : (38753 / 250000000) ≤ -Real.log (199969 / 200000) ∧
    -Real.log (199969 / 200000) ≤ (155013 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 399969)) (n := 12)
    (lo := (38753 / 250000000)) (hi := (155013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199969) = 1/(199969 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_660 : Bounds (-155013 / 1000000000) (-38753 / 250000000) (Real.log (199969 / 200000)) := by
  have h := reflection_log_660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_661_neg : (74838419 / 1000000000) ≤ -Real.log (100000 / 107771) ∧
    -Real.log (100000 / 107771) ≤ (3741921 / 50000000) := by
  have h := checkLog_sound (w := (7771 / 207771)) (n := 12)
    (lo := (74838419 / 1000000000)) (hi := (3741921 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107771 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107771 / 100000) = 1/(100000 / 107771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_661 : Bounds (74838419 / 1000000000) (3741921 / 50000000) (Real.log (107771 / 100000)) := by
  have h := reflection_log_661_neg
  have he : Real.log (107771 / 100000) = -Real.log (100000 / 107771) := by
    rw [show ((107771 / 100000) : ℝ) = ((100000 / 107771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_662_neg : (80895571 / 1000000000) ≤ -Real.log (92229 / 100000) ∧
    -Real.log (92229 / 100000) ≤ (20223893 / 250000000) := by
  have h := checkLog_sound (w := (7771 / 192229)) (n := 12)
    (lo := (80895571 / 1000000000)) (hi := (20223893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92229) = 1/(92229 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_662 : Bounds (-20223893 / 250000000) (-80895571 / 1000000000) (Real.log (92229 / 100000)) := by
  have h := reflection_log_662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_663_neg : (75029547 / 1000000000) ≤ -Real.log (250000 / 269479) ∧
    -Real.log (250000 / 269479) ≤ (18757387 / 250000000) := by
  have h := checkLog_sound (w := (19479 / 519479)) (n := 12)
    (lo := (75029547 / 1000000000)) (hi := (18757387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269479 / 250000) = 1/(250000 / 269479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_663 : Bounds (75029547 / 1000000000) (18757387 / 250000000) (Real.log (269479 / 250000)) := by
  have h := reflection_log_663_neg
  have he : Real.log (269479 / 250000) = -Real.log (250000 / 269479) := by
    rw [show ((269479 / 250000) : ℝ) = ((250000 / 269479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_664_neg : (81118953 / 1000000000) ≤ -Real.log (230521 / 250000) ∧
    -Real.log (230521 / 250000) ≤ (40559477 / 500000000) := by
  have h := checkLog_sound (w := (19479 / 480521)) (n := 12)
    (lo := (81118953 / 1000000000)) (hi := (40559477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230521) = 1/(230521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_664 : Bounds (-40559477 / 500000000) (-81118953 / 1000000000) (Real.log (230521 / 250000)) := by
  have h := reflection_log_664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_665_neg : (1217881 / 200000000) ≤ -Real.log (62120568559 / 62500000000) ∧
    -Real.log (62120568559 / 62500000000) ≤ (3044703 / 500000000) := by
  have h := checkLog_sound (w := (379431441 / 124620568559)) (n := 12)
    (lo := (1217881 / 200000000)) (hi := (3044703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62120568559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62120568559) = 1/(62120568559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_665 : Bounds (-3044703 / 500000000) (-1217881 / 200000000) (Real.log (62120568559 / 62500000000)) := by
  have h := reflection_log_665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_666_neg : (6057151 / 1000000000) ≤ -Real.log (9939611559 / 10000000000) ∧
    -Real.log (9939611559 / 10000000000) ≤ (94643 / 15625000) := by
  have h := checkLog_sound (w := (60388441 / 19939611559)) (n := 12)
    (lo := (6057151 / 1000000000)) (hi := (94643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9939611559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9939611559) = 1/(9939611559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_666 : Bounds (-94643 / 15625000) (-6057151 / 1000000000) (Real.log (9939611559 / 10000000000)) := by
  have h := reflection_log_666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_667_neg : (15573399 / 100000000) ≤ -Real.log (500000000000 / 584257662991) ∧
    -Real.log (500000000000 / 584257662991) ≤ (155733991 / 1000000000) := by
  have h := checkLog_sound (w := (84257662991 / 1084257662991)) (n := 12)
    (lo := (15573399 / 100000000)) (hi := (155733991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584257662991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584257662991 / 500000000000) = 1/(500000000000 / 584257662991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_667 : Bounds (15573399 / 100000000) (155733991 / 1000000000) (Real.log (584257662991 / 500000000000)) := by
  have h := reflection_log_667_neg
  have he : Real.log (584257662991 / 500000000000) = -Real.log (500000000000 / 584257662991) := by
    rw [show ((584257662991 / 500000000000) : ℝ) = ((500000000000 / 584257662991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_668_neg : (312297 / 2000000) ≤ -Real.log (12500000000 / 14612497343) ∧
    -Real.log (12500000000 / 14612497343) ≤ (156148501 / 1000000000) := by
  have h := checkLog_sound (w := (2112497343 / 27112497343)) (n := 12)
    (lo := (312297 / 2000000)) (hi := (156148501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14612497343 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14612497343 / 12500000000) = 1/(12500000000 / 14612497343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_668 : Bounds (312297 / 2000000) (156148501 / 1000000000) (Real.log (14612497343 / 12500000000)) := by
  have h := reflection_log_668_neg
  have he : Real.log (14612497343 / 12500000000) = -Real.log (12500000000 / 14612497343) := by
    rw [show ((14612497343 / 12500000000) : ℝ) = ((12500000000 / 14612497343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_669_neg : (12492563 / 40000000) ≤ -Real.log (125000000000 / 170822979529) ∧
    -Real.log (125000000000 / 170822979529) ≤ (78078519 / 250000000) := by
  have h := checkLog_sound (w := (45822979529 / 295822979529)) (n := 12)
    (lo := (12492563 / 40000000)) (hi := (78078519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170822979529 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170822979529 / 125000000000) = 1/(125000000000 / 170822979529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_669 : Bounds (12492563 / 40000000) (78078519 / 250000000) (Real.log (170822979529 / 125000000000)) := by
  have h := reflection_log_669_neg
  have he : Real.log (170822979529 / 125000000000) = -Real.log (125000000000 / 170822979529) := by
    rw [show ((170822979529 / 125000000000) : ℝ) = ((125000000000 / 170822979529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_670_neg : (62503799 / 200000000) ≤ -Real.log (500000000000 / 683431952663) ∧
    -Real.log (500000000000 / 683431952663) ≤ (78129749 / 250000000) := by
  have h := checkLog_sound (w := (183431952663 / 1183431952663)) (n := 12)
    (lo := (62503799 / 200000000)) (hi := (78129749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683431952663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683431952663 / 500000000000) = 1/(500000000000 / 683431952663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_670 : Bounds (62503799 / 200000000) (78129749 / 250000000) (Real.log (683431952663 / 500000000000)) := by
  have h := reflection_log_670_neg
  have he : Real.log (683431952663 / 500000000000) = -Real.log (500000000000 / 683431952663) := by
    rw [show ((683431952663 / 500000000000) : ℝ) = ((500000000000 / 683431952663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_671_neg : (3604673 / 25000000) ≤ -Real.log (10000 / 11551) ∧
    -Real.log (10000 / 11551) ≤ (144186921 / 1000000000) := by
  have h := checkLog_sound (w := (1551 / 21551)) (n := 12)
    (lo := (3604673 / 25000000)) (hi := (144186921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11551 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11551 / 10000) = 1/(10000 / 11551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_671 : Bounds (3604673 / 25000000) (144186921 / 1000000000) (Real.log (11551 / 10000)) := by
  have h := reflection_log_671_neg
  have he : Real.log (11551 / 10000) = -Real.log (10000 / 11551) := by
    rw [show ((11551 / 10000) : ℝ) = ((10000 / 11551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_672_neg : (168537001 / 1000000000) ≤ -Real.log (8449 / 10000) ∧
    -Real.log (8449 / 10000) ≤ (84268501 / 500000000) := by
  have h := checkLog_sound (w := (1551 / 18449)) (n := 12)
    (lo := (168537001 / 1000000000)) (hi := (84268501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8449) = 1/(8449 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_672 : Bounds (-84268501 / 500000000) (-168537001 / 1000000000) (Real.log (8449 / 10000)) := by
  have h := reflection_log_672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_673_neg : (155087 / 1000000000) ≤ -Real.log (10000000 / 10001551) ∧
    -Real.log (10000000 / 10001551) ≤ (9693 / 62500000) := by
  have h := checkLog_sound (w := (1551 / 20001551)) (n := 12)
    (lo := (155087 / 1000000000)) (hi := (9693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001551 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001551 / 10000000) = 1/(10000000 / 10001551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_673 : Bounds (155087 / 1000000000) (9693 / 62500000) (Real.log (10001551 / 10000000)) := by
  have h := reflection_log_673_neg
  have he : Real.log (10001551 / 10000000) = -Real.log (10000000 / 10001551) := by
    rw [show ((10001551 / 10000000) : ℝ) = ((10000000 / 10001551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_674_neg : (19389 / 125000000) ≤ -Real.log (9998449 / 10000000) ∧
    -Real.log (9998449 / 10000000) ≤ (155113 / 1000000000) := by
  have h := checkLog_sound (w := (1551 / 19998449)) (n := 12)
    (lo := (19389 / 125000000)) (hi := (155113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998449) = 1/(9998449 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_674 : Bounds (-155113 / 1000000000) (-19389 / 125000000) (Real.log (9998449 / 10000000)) := by
  have h := reflection_log_674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_675_neg : (74884813 / 1000000000) ≤ -Real.log (3125 / 3368) ∧
    -Real.log (3125 / 3368) ≤ (37442407 / 500000000) := by
  have h := checkLog_sound (w := (243 / 6493)) (n := 12)
    (lo := (74884813 / 1000000000)) (hi := (37442407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3368 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3368 / 3125) = 1/(3125 / 3368) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_675 : Bounds (74884813 / 1000000000) (37442407 / 500000000) (Real.log (3368 / 3125)) := by
  have h := reflection_log_675_neg
  have he : Real.log (3368 / 3125) = -Real.log (3125 / 3368) := by
    rw [show ((3368 / 3125) : ℝ) = ((3125 / 3368) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_676_neg : (16189957 / 200000000) ≤ -Real.log (2882 / 3125) ∧
    -Real.log (2882 / 3125) ≤ (40474893 / 500000000) := by
  have h := checkLog_sound (w := (243 / 6007)) (n := 12)
    (lo := (16189957 / 200000000)) (hi := (40474893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2882) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2882) = 1/(2882 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_676 : Bounds (-40474893 / 500000000) (-16189957 / 200000000) (Real.log (2882 / 3125)) := by
  have h := reflection_log_676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_677_neg : (75076859 / 1000000000) ≤ -Real.log (1000000 / 1077967) ∧
    -Real.log (1000000 / 1077967) ≤ (3753843 / 50000000) := by
  have h := checkLog_sound (w := (77967 / 2077967)) (n := 12)
    (lo := (75076859 / 1000000000)) (hi := (3753843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077967 / 1000000) = 1/(1000000 / 1077967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_677 : Bounds (75076859 / 1000000000) (3753843 / 50000000) (Real.log (1077967 / 1000000)) := by
  have h := reflection_log_677_neg
  have he : Real.log (1077967 / 1000000) = -Real.log (1000000 / 1077967) := by
    rw [show ((1077967 / 1000000) : ℝ) = ((1000000 / 1077967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_678_neg : (10146783 / 125000000) ≤ -Real.log (922033 / 1000000) ∧
    -Real.log (922033 / 1000000) ≤ (16234853 / 200000000) := by
  have h := checkLog_sound (w := (77967 / 1922033)) (n := 12)
    (lo := (10146783 / 125000000)) (hi := (16234853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922033) = 1/(922033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_678 : Bounds (-16234853 / 200000000) (-10146783 / 125000000) (Real.log (922033 / 1000000)) := by
  have h := reflection_log_678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_679_neg : (1524351 / 250000000) ≤ -Real.log (993921146911 / 1000000000000) ∧
    -Real.log (993921146911 / 1000000000000) ≤ (1219481 / 200000000) := by
  have h := checkLog_sound (w := (6078853089 / 1993921146911)) (n := 12)
    (lo := (1524351 / 250000000)) (hi := (1219481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993921146911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993921146911) = 1/(993921146911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_679 : Bounds (-1219481 / 200000000) (-1524351 / 250000000) (Real.log (993921146911 / 1000000000000)) := by
  have h := reflection_log_679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_680_neg : (1516243 / 250000000) ≤ -Real.log (9706576 / 9765625) ∧
    -Real.log (9706576 / 9765625) ≤ (6064973 / 1000000000) := by
  have h := checkLog_sound (w := (59049 / 19472201)) (n := 12)
    (lo := (1516243 / 250000000)) (hi := (6064973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9706576) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9706576) = 1/(9706576 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_680 : Bounds (-6064973 / 1000000000) (-1516243 / 250000000) (Real.log (9706576 / 9765625)) := by
  have h := reflection_log_680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_681_neg : (77917299 / 500000000) ≤ -Real.log (500000000000 / 584316446911) ∧
    -Real.log (500000000000 / 584316446911) ≤ (155834599 / 1000000000) := by
  have h := checkLog_sound (w := (84316446911 / 1084316446911)) (n := 12)
    (lo := (77917299 / 500000000)) (hi := (155834599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584316446911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584316446911 / 500000000000) = 1/(500000000000 / 584316446911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_681 : Bounds (77917299 / 500000000) (155834599 / 1000000000) (Real.log (584316446911 / 500000000000)) := by
  have h := reflection_log_681_neg
  have he : Real.log (584316446911 / 500000000000) = -Real.log (500000000000 / 584316446911) := by
    rw [show ((584316446911 / 500000000000) : ℝ) = ((500000000000 / 584316446911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_682_neg : (39062781 / 250000000) ≤ -Real.log (250000000000 / 292279940089) ∧
    -Real.log (250000000000 / 292279940089) ≤ (1250009 / 8000000) := by
  have h := checkLog_sound (w := (42279940089 / 542279940089)) (n := 12)
    (lo := (39062781 / 250000000)) (hi := (1250009 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292279940089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292279940089 / 250000000000) = 1/(250000000000 / 292279940089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_682 : Bounds (39062781 / 250000000) (1250009 / 8000000) (Real.log (292279940089 / 250000000000)) := by
  have h := reflection_log_682_neg
  have he : Real.log (292279940089 / 250000000000) = -Real.log (250000000000 / 292279940089) := by
    rw [show ((292279940089 / 250000000000) : ℝ) = ((250000000000 / 292279940089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_683_neg : (62503799 / 200000000) ≤ -Real.log (250000000000 / 341715976331) ∧
    -Real.log (250000000000 / 341715976331) ≤ (78129749 / 250000000) := by
  have h := checkLog_sound (w := (91715976331 / 591715976331)) (n := 12)
    (lo := (62503799 / 200000000)) (hi := (78129749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341715976331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341715976331 / 250000000000) = 1/(250000000000 / 341715976331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_683 : Bounds (62503799 / 200000000) (78129749 / 250000000) (Real.log (341715976331 / 250000000000)) := by
  have h := reflection_log_683_neg
  have he : Real.log (341715976331 / 250000000000) = -Real.log (250000000000 / 341715976331) := by
    rw [show ((341715976331 / 250000000000) : ℝ) = ((250000000000 / 341715976331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_684_neg : (156361961 / 500000000) ≤ -Real.log (250000000000 / 341786010179) ∧
    -Real.log (250000000000 / 341786010179) ≤ (312723923 / 1000000000) := by
  have h := checkLog_sound (w := (91786010179 / 591786010179)) (n := 12)
    (lo := (156361961 / 500000000)) (hi := (312723923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341786010179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341786010179 / 250000000000) = 1/(250000000000 / 341786010179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_684 : Bounds (156361961 / 500000000) (312723923 / 1000000000) (Real.log (341786010179 / 250000000000)) := by
  have h := reflection_log_684_neg
  have he : Real.log (341786010179 / 250000000000) = -Real.log (250000000000 / 341786010179) := by
    rw [show ((341786010179 / 250000000000) : ℝ) = ((250000000000 / 341786010179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_685_neg : (144273489 / 1000000000) ≤ -Real.log (625 / 722) ∧
    -Real.log (625 / 722) ≤ (14427349 / 100000000) := by
  have h := checkLog_sound (w := (97 / 1347)) (n := 12)
    (lo := (144273489 / 1000000000)) (hi := (14427349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722 / 625) = 1/(625 / 722) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_685 : Bounds (144273489 / 1000000000) (14427349 / 100000000) (Real.log (722 / 625)) := by
  have h := reflection_log_685_neg
  have he : Real.log (722 / 625) = -Real.log (625 / 722) := by
    rw [show ((722 / 625) : ℝ) = ((625 / 722) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_686_neg : (84327683 / 500000000) ≤ -Real.log (528 / 625) ∧
    -Real.log (528 / 625) ≤ (168655367 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 1153)) (n := 12)
    (lo := (84327683 / 500000000)) (hi := (168655367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 528) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 528) = 1/(528 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_686 : Bounds (-168655367 / 1000000000) (-84327683 / 500000000) (Real.log (528 / 625)) := by
  have h := reflection_log_686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_687_neg : (155187 / 1000000000) ≤ -Real.log (625000 / 625097) ∧
    -Real.log (625000 / 625097) ≤ (38797 / 250000000) := by
  have h := checkLog_sound (w := (97 / 1250097)) (n := 12)
    (lo := (155187 / 1000000000)) (hi := (38797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625097 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625097 / 625000) = 1/(625000 / 625097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_687 : Bounds (155187 / 1000000000) (38797 / 250000000) (Real.log (625097 / 625000)) := by
  have h := reflection_log_687_neg
  have he : Real.log (625097 / 625000) = -Real.log (625000 / 625097) := by
    rw [show ((625097 / 625000) : ℝ) = ((625000 / 625097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_688_neg : (38803 / 250000000) ≤ -Real.log (624903 / 625000) ∧
    -Real.log (624903 / 625000) ≤ (155213 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 1249903)) (n := 12)
    (lo := (38803 / 250000000)) (hi := (155213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624903) = 1/(624903 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_688 : Bounds (-155213 / 1000000000) (-38803 / 250000000) (Real.log (624903 / 625000)) := by
  have h := reflection_log_688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_689_neg : (18733033 / 250000000) ≤ -Real.log (1000000 / 1077811) ∧
    -Real.log (1000000 / 1077811) ≤ (74932133 / 1000000000) := by
  have h := checkLog_sound (w := (77811 / 2077811)) (n := 12)
    (lo := (18733033 / 250000000)) (hi := (74932133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077811 / 1000000) = 1/(1000000 / 1077811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_689 : Bounds (18733033 / 250000000) (74932133 / 1000000000) (Real.log (1077811 / 1000000)) := by
  have h := reflection_log_689_neg
  have he : Real.log (1077811 / 1000000) = -Real.log (1000000 / 1077811) := by
    rw [show ((1077811 / 1000000) : ℝ) = ((1000000 / 1077811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_690_neg : (81005087 / 1000000000) ≤ -Real.log (922189 / 1000000) ∧
    -Real.log (922189 / 1000000) ≤ (2531409 / 31250000) := by
  have h := checkLog_sound (w := (77811 / 1922189)) (n := 12)
    (lo := (81005087 / 1000000000)) (hi := (2531409 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922189) = 1/(922189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_690 : Bounds (-2531409 / 31250000) (-81005087 / 1000000000) (Real.log (922189 / 1000000)) := by
  have h := reflection_log_690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_691_neg : (37561621 / 500000000) ≤ -Real.log (1000000 / 1078017) ∧
    -Real.log (1000000 / 1078017) ≤ (75123243 / 1000000000) := by
  have h := checkLog_sound (w := (78017 / 2078017)) (n := 12)
    (lo := (37561621 / 500000000)) (hi := (75123243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078017 / 1000000) = 1/(1000000 / 1078017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_691 : Bounds (37561621 / 500000000) (75123243 / 1000000000) (Real.log (1078017 / 1000000)) := by
  have h := reflection_log_691_neg
  have he : Real.log (1078017 / 1000000) = -Real.log (1000000 / 1078017) := by
    rw [show ((1078017 / 1000000) : ℝ) = ((1000000 / 1078017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_692_neg : (81228493 / 1000000000) ≤ -Real.log (921983 / 1000000) ∧
    -Real.log (921983 / 1000000) ≤ (40614247 / 500000000) := by
  have h := checkLog_sound (w := (78017 / 1921983)) (n := 12)
    (lo := (81228493 / 1000000000)) (hi := (40614247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921983) = 1/(921983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_692 : Bounds (-40614247 / 500000000) (-81228493 / 1000000000) (Real.log (921983 / 1000000)) := by
  have h := reflection_log_692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_693_neg : (6105251 / 1000000000) ≤ -Real.log (993913347711 / 1000000000000) ∧
    -Real.log (993913347711 / 1000000000000) ≤ (1526313 / 250000000) := by
  have h := checkLog_sound (w := (6086652289 / 1993913347711)) (n := 12)
    (lo := (6105251 / 1000000000)) (hi := (1526313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993913347711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993913347711) = 1/(993913347711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_693 : Bounds (-1526313 / 250000000) (-6105251 / 1000000000) (Real.log (993913347711 / 1000000000000)) := by
  have h := reflection_log_693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_694_neg : (3036477 / 500000000) ≤ -Real.log (993945448279 / 1000000000000) ∧
    -Real.log (993945448279 / 1000000000000) ≤ (1214591 / 200000000) := by
  have h := checkLog_sound (w := (6054551721 / 1993945448279)) (n := 12)
    (lo := (3036477 / 500000000)) (hi := (1214591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993945448279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993945448279) = 1/(993945448279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_694 : Bounds (-1214591 / 200000000) (-3036477 / 500000000) (Real.log (993945448279 / 1000000000000)) := by
  have h := reflection_log_694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_695_neg : (155937219 / 1000000000) ≤ -Real.log (250000000000 / 292188206539) ∧
    -Real.log (250000000000 / 292188206539) ≤ (7796861 / 50000000) := by
  have h := checkLog_sound (w := (42188206539 / 542188206539)) (n := 12)
    (lo := (155937219 / 1000000000)) (hi := (7796861 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292188206539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292188206539 / 250000000000) = 1/(250000000000 / 292188206539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_695 : Bounds (155937219 / 1000000000) (7796861 / 50000000) (Real.log (292188206539 / 250000000000)) := by
  have h := reflection_log_695_neg
  have he : Real.log (292188206539 / 250000000000) = -Real.log (250000000000 / 292188206539) := by
    rw [show ((292188206539 / 250000000000) : ℝ) = ((250000000000 / 292188206539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_696_neg : (19543967 / 125000000) ≤ -Real.log (160000000 / 187077983) ∧
    -Real.log (160000000 / 187077983) ≤ (156351737 / 1000000000) := by
  have h := checkLog_sound (w := (27077983 / 347077983)) (n := 12)
    (lo := (19543967 / 125000000)) (hi := (156351737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187077983 / 160000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187077983 / 160000000) = 1/(160000000 / 187077983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_696 : Bounds (19543967 / 125000000) (156351737 / 1000000000) (Real.log (187077983 / 160000000)) := by
  have h := reflection_log_696_neg
  have he : Real.log (187077983 / 160000000) = -Real.log (160000000 / 187077983) := by
    rw [show ((187077983 / 160000000) : ℝ) = ((160000000 / 187077983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_697_neg : (156361961 / 500000000) ≤ -Real.log (500000000000 / 683572020357) ∧
    -Real.log (500000000000 / 683572020357) ≤ (312723923 / 1000000000) := by
  have h := checkLog_sound (w := (183572020357 / 1183572020357)) (n := 12)
    (lo := (156361961 / 500000000)) (hi := (312723923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683572020357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683572020357 / 500000000000) = 1/(500000000000 / 683572020357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_697 : Bounds (156361961 / 500000000) (312723923 / 1000000000) (Real.log (683572020357 / 500000000000)) := by
  have h := reflection_log_697_neg
  have he : Real.log (683572020357 / 500000000000) = -Real.log (500000000000 / 683572020357) := by
    rw [show ((683572020357 / 500000000000) : ℝ) = ((500000000000 / 683572020357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_698_neg : (62585771 / 200000000) ≤ -Real.log (500000000000 / 683712121213) ∧
    -Real.log (500000000000 / 683712121213) ≤ (39116107 / 125000000) := by
  have h := checkLog_sound (w := (183712121213 / 1183712121213)) (n := 12)
    (lo := (62585771 / 200000000)) (hi := (39116107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683712121213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683712121213 / 500000000000) = 1/(500000000000 / 683712121213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_698 : Bounds (62585771 / 200000000) (39116107 / 125000000) (Real.log (683712121213 / 500000000000)) := by
  have h := reflection_log_698_neg
  have he : Real.log (683712121213 / 500000000000) = -Real.log (500000000000 / 683712121213) := by
    rw [show ((683712121213 / 500000000000) : ℝ) = ((500000000000 / 683712121213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_699_neg : (2887201 / 20000000) ≤ -Real.log (10000 / 11553) ∧
    -Real.log (10000 / 11553) ≤ (144360051 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 21553)) (n := 12)
    (lo := (2887201 / 20000000)) (hi := (144360051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11553 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11553 / 10000) = 1/(10000 / 11553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_699 : Bounds (2887201 / 20000000) (144360051 / 1000000000) (Real.log (11553 / 10000)) := by
  have h := reflection_log_699_neg
  have he : Real.log (11553 / 10000) = -Real.log (10000 / 11553) := by
    rw [show ((11553 / 10000) : ℝ) = ((10000 / 11553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_700_neg : (10548359 / 62500000) ≤ -Real.log (8447 / 10000) ∧
    -Real.log (8447 / 10000) ≤ (33754749 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 18447)) (n := 12)
    (lo := (10548359 / 62500000)) (hi := (33754749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8447) = 1/(8447 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_700 : Bounds (-33754749 / 200000000) (-10548359 / 62500000) (Real.log (8447 / 10000)) := by
  have h := reflection_log_700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_701_neg : (155287 / 1000000000) ≤ -Real.log (10000000 / 10001553) ∧
    -Real.log (10000000 / 10001553) ≤ (19411 / 125000000) := by
  have h := checkLog_sound (w := (1553 / 20001553)) (n := 12)
    (lo := (155287 / 1000000000)) (hi := (19411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001553 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001553 / 10000000) = 1/(10000000 / 10001553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_701 : Bounds (155287 / 1000000000) (19411 / 125000000) (Real.log (10001553 / 10000000)) := by
  have h := reflection_log_701_neg
  have he : Real.log (10001553 / 10000000) = -Real.log (10000000 / 10001553) := by
    rw [show ((10001553 / 10000000) : ℝ) = ((10000000 / 10001553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_702_neg : (9707 / 62500000) ≤ -Real.log (9998447 / 10000000) ∧
    -Real.log (9998447 / 10000000) ≤ (155313 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 19998447)) (n := 12)
    (lo := (9707 / 62500000)) (hi := (155313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998447) = 1/(9998447 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_702 : Bounds (-155313 / 1000000000) (-9707 / 62500000) (Real.log (9998447 / 10000000)) := by
  have h := reflection_log_702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_703_neg : (74979449 / 1000000000) ≤ -Real.log (500000 / 538931) ∧
    -Real.log (500000 / 538931) ≤ (1499589 / 20000000) := by
  have h := checkLog_sound (w := (38931 / 1038931)) (n := 12)
    (lo := (74979449 / 1000000000)) (hi := (1499589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538931 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538931 / 500000) = 1/(500000 / 538931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_703 : Bounds (74979449 / 1000000000) (1499589 / 20000000) (Real.log (538931 / 500000)) := by
  have h := reflection_log_703_neg
  have he : Real.log (538931 / 500000) = -Real.log (500000 / 538931) := by
    rw [show ((538931 / 500000) : ℝ) = ((500000 / 538931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0011 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_704_neg : (10132549 / 125000000) ≤ -Real.log (461069 / 500000) ∧
    -Real.log (461069 / 500000) ≤ (81060393 / 1000000000) := by
  have h := checkLog_sound (w := (38931 / 961069)) (n := 12)
    (lo := (10132549 / 125000000)) (hi := (81060393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461069) = 1/(461069 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_704 : Bounds (-81060393 / 1000000000) (-10132549 / 125000000) (Real.log (461069 / 500000)) := by
  have h := reflection_log_704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_705_neg : (1503411 / 20000000) ≤ -Real.log (250000 / 269517) ∧
    -Real.log (250000 / 269517) ≤ (75170551 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 519517)) (n := 12)
    (lo := (1503411 / 20000000)) (hi := (75170551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269517 / 250000) = 1/(250000 / 269517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_705 : Bounds (1503411 / 20000000) (75170551 / 1000000000) (Real.log (269517 / 250000)) := by
  have h := reflection_log_705_neg
  have he : Real.log (269517 / 250000) = -Real.log (250000 / 269517) := by
    rw [show ((269517 / 250000) : ℝ) = ((250000 / 269517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_706_neg : (8128381 / 100000000) ≤ -Real.log (230483 / 250000) ∧
    -Real.log (230483 / 250000) ≤ (81283811 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 480483)) (n := 12)
    (lo := (8128381 / 100000000)) (hi := (81283811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230483) = 1/(230483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_706 : Bounds (-81283811 / 1000000000) (-8128381 / 100000000) (Real.log (230483 / 250000)) := by
  have h := reflection_log_706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_707_neg : (305663 / 50000000) ≤ -Real.log (62119086711 / 62500000000) ∧
    -Real.log (62119086711 / 62500000000) ≤ (6113261 / 1000000000) := by
  have h := checkLog_sound (w := (380913289 / 124619086711)) (n := 12)
    (lo := (305663 / 50000000)) (hi := (6113261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62119086711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62119086711) = 1/(62119086711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_707 : Bounds (-6113261 / 1000000000) (-305663 / 50000000) (Real.log (62119086711 / 62500000000)) := by
  have h := reflection_log_707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_708_neg : (3040471 / 500000000) ≤ -Real.log (248484377239 / 250000000000) ∧
    -Real.log (248484377239 / 250000000000) ≤ (6080943 / 1000000000) := by
  have h := checkLog_sound (w := (1515622761 / 498484377239)) (n := 12)
    (lo := (3040471 / 500000000)) (hi := (6080943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248484377239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248484377239) = 1/(248484377239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_708 : Bounds (-6080943 / 1000000000) (-3040471 / 500000000) (Real.log (248484377239 / 250000000000)) := by
  have h := reflection_log_708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_709_neg : (156039841 / 1000000000) ≤ -Real.log (500000000000 / 584436385877) ∧
    -Real.log (500000000000 / 584436385877) ≤ (78019921 / 500000000) := by
  have h := checkLog_sound (w := (84436385877 / 1084436385877)) (n := 12)
    (lo := (156039841 / 1000000000)) (hi := (78019921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584436385877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584436385877 / 500000000000) = 1/(500000000000 / 584436385877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_709 : Bounds (156039841 / 1000000000) (78019921 / 500000000) (Real.log (584436385877 / 500000000000)) := by
  have h := reflection_log_709_neg
  have he : Real.log (584436385877 / 500000000000) = -Real.log (500000000000 / 584436385877) := by
    rw [show ((584436385877 / 500000000000) : ℝ) = ((500000000000 / 584436385877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_710_neg : (156454361 / 1000000000) ≤ -Real.log (500000000000 / 584678696477) ∧
    -Real.log (500000000000 / 584678696477) ≤ (78227181 / 500000000) := by
  have h := checkLog_sound (w := (84678696477 / 1084678696477)) (n := 12)
    (lo := (156454361 / 1000000000)) (hi := (78227181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584678696477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584678696477 / 500000000000) = 1/(500000000000 / 584678696477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_710 : Bounds (156454361 / 1000000000) (78227181 / 500000000) (Real.log (584678696477 / 500000000000)) := by
  have h := reflection_log_710_neg
  have he : Real.log (584678696477 / 500000000000) = -Real.log (500000000000 / 584678696477) := by
    rw [show ((584678696477 / 500000000000) : ℝ) = ((500000000000 / 584678696477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_711_neg : (62585771 / 200000000) ≤ -Real.log (125000000000 / 170928030303) ∧
    -Real.log (125000000000 / 170928030303) ≤ (39116107 / 125000000) := by
  have h := checkLog_sound (w := (45928030303 / 295928030303)) (n := 12)
    (lo := (62585771 / 200000000)) (hi := (39116107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170928030303 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170928030303 / 125000000000) = 1/(125000000000 / 170928030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_711 : Bounds (62585771 / 200000000) (39116107 / 125000000) (Real.log (170928030303 / 125000000000)) := by
  have h := reflection_log_711_neg
  have he : Real.log (170928030303 / 125000000000) = -Real.log (125000000000 / 170928030303) := by
    rw [show ((170928030303 / 125000000000) : ℝ) = ((125000000000 / 170928030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_712_neg : (156566897 / 500000000) ≤ -Real.log (500000000000 / 683852255239) ∧
    -Real.log (500000000000 / 683852255239) ≤ (62626759 / 200000000) := by
  have h := checkLog_sound (w := (183852255239 / 1183852255239)) (n := 12)
    (lo := (156566897 / 500000000)) (hi := (62626759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683852255239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683852255239 / 500000000000) = 1/(500000000000 / 683852255239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_712 : Bounds (156566897 / 500000000) (62626759 / 200000000) (Real.log (683852255239 / 500000000000)) := by
  have h := reflection_log_712_neg
  have he : Real.log (683852255239 / 500000000000) = -Real.log (500000000000 / 683852255239) := by
    rw [show ((683852255239 / 500000000000) : ℝ) = ((500000000000 / 683852255239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_713_neg : (36111651 / 250000000) ≤ -Real.log (5000 / 5777) ∧
    -Real.log (5000 / 5777) ≤ (28889321 / 200000000) := by
  have h := checkLog_sound (w := (777 / 10777)) (n := 12)
    (lo := (36111651 / 250000000)) (hi := (28889321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5777 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5777 / 5000) = 1/(5000 / 5777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_713 : Bounds (36111651 / 250000000) (28889321 / 200000000) (Real.log (5777 / 5000)) := by
  have h := reflection_log_713_neg
  have he : Real.log (5777 / 5000) = -Real.log (5000 / 5777) := by
    rw [show ((5777 / 5000) : ℝ) = ((5000 / 5777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_714_neg : (21111517 / 125000000) ≤ -Real.log (4223 / 5000) ∧
    -Real.log (4223 / 5000) ≤ (168892137 / 1000000000) := by
  have h := checkLog_sound (w := (777 / 9223)) (n := 12)
    (lo := (21111517 / 125000000)) (hi := (168892137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4223) = 1/(4223 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_714 : Bounds (-168892137 / 1000000000) (-21111517 / 125000000) (Real.log (4223 / 5000)) := by
  have h := reflection_log_714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_715_neg : (155387 / 1000000000) ≤ -Real.log (5000000 / 5000777) ∧
    -Real.log (5000000 / 5000777) ≤ (38847 / 250000000) := by
  have h := checkLog_sound (w := (777 / 10000777)) (n := 12)
    (lo := (155387 / 1000000000)) (hi := (38847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000777 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000777 / 5000000) = 1/(5000000 / 5000777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_715 : Bounds (155387 / 1000000000) (38847 / 250000000) (Real.log (5000777 / 5000000)) := by
  have h := reflection_log_715_neg
  have he : Real.log (5000777 / 5000000) = -Real.log (5000000 / 5000777) := by
    rw [show ((5000777 / 5000000) : ℝ) = ((5000000 / 5000777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_716_neg : (38853 / 250000000) ≤ -Real.log (4999223 / 5000000) ∧
    -Real.log (4999223 / 5000000) ≤ (155413 / 1000000000) := by
  have h := checkLog_sound (w := (777 / 9999223)) (n := 12)
    (lo := (38853 / 250000000)) (hi := (155413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999223) = 1/(4999223 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_716 : Bounds (-155413 / 1000000000) (-38853 / 250000000) (Real.log (4999223 / 5000000)) := by
  have h := reflection_log_716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_717_neg : (18756459 / 250000000) ≤ -Real.log (125000 / 134739) ∧
    -Real.log (125000 / 134739) ≤ (75025837 / 1000000000) := by
  have h := checkLog_sound (w := (9739 / 259739)) (n := 12)
    (lo := (18756459 / 250000000)) (hi := (75025837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134739 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134739 / 125000) = 1/(125000 / 134739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_717 : Bounds (18756459 / 250000000) (75025837 / 1000000000) (Real.log (134739 / 125000)) := by
  have h := reflection_log_717_neg
  have he : Real.log (134739 / 125000) = -Real.log (125000 / 134739) := by
    rw [show ((134739 / 125000) : ℝ) = ((125000 / 134739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_718_neg : (16222923 / 200000000) ≤ -Real.log (115261 / 125000) ∧
    -Real.log (115261 / 125000) ≤ (10139327 / 125000000) := by
  have h := checkLog_sound (w := (9739 / 240261)) (n := 12)
    (lo := (16222923 / 200000000)) (hi := (10139327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115261) = 1/(115261 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_718 : Bounds (-10139327 / 125000000) (-16222923 / 200000000) (Real.log (115261 / 125000)) := by
  have h := reflection_log_718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_719_neg : (1175279 / 15625000) ≤ -Real.log (1000000 / 1078119) ∧
    -Real.log (1000000 / 1078119) ≤ (75217857 / 1000000000) := by
  have h := checkLog_sound (w := (78119 / 2078119)) (n := 12)
    (lo := (1175279 / 15625000)) (hi := (75217857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078119 / 1000000) = 1/(1000000 / 1078119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_719 : Bounds (1175279 / 15625000) (75217857 / 1000000000) (Real.log (1078119 / 1000000)) := by
  have h := reflection_log_719_neg
  have he : Real.log (1078119 / 1000000) = -Real.log (1000000 / 1078119) := by
    rw [show ((1078119 / 1000000) : ℝ) = ((1000000 / 1078119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_720_neg : (81339131 / 1000000000) ≤ -Real.log (921881 / 1000000) ∧
    -Real.log (921881 / 1000000) ≤ (20334783 / 250000000) := by
  have h := checkLog_sound (w := (78119 / 1921881)) (n := 12)
    (lo := (81339131 / 1000000000)) (hi := (20334783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921881) = 1/(921881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_720 : Bounds (-20334783 / 250000000) (-81339131 / 1000000000) (Real.log (921881 / 1000000)) := by
  have h := reflection_log_720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_721_neg : (3060637 / 500000000) ≤ -Real.log (993897421839 / 1000000000000) ∧
    -Real.log (993897421839 / 1000000000000) ≤ (244851 / 40000000) := by
  have h := checkLog_sound (w := (6102578161 / 1993897421839)) (n := 12)
    (lo := (3060637 / 500000000)) (hi := (244851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993897421839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993897421839) = 1/(993897421839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_721 : Bounds (-244851 / 40000000) (-3060637 / 500000000) (Real.log (993897421839 / 1000000000000)) := by
  have h := reflection_log_721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_722_neg : (3044389 / 500000000) ≤ -Real.log (15530151879 / 15625000000) ∧
    -Real.log (15530151879 / 15625000000) ≤ (6088779 / 1000000000) := by
  have h := checkLog_sound (w := (94848121 / 31155151879)) (n := 12)
    (lo := (3044389 / 500000000)) (hi := (6088779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15530151879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15530151879) = 1/(15530151879 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_722 : Bounds (-6088779 / 1000000000) (-3044389 / 500000000) (Real.log (15530151879 / 15625000000)) := by
  have h := reflection_log_722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_723_neg : (156140451 / 1000000000) ≤ -Real.log (500000000000 / 584495189179) ∧
    -Real.log (500000000000 / 584495189179) ≤ (39035113 / 250000000) := by
  have h := checkLog_sound (w := (84495189179 / 1084495189179)) (n := 12)
    (lo := (156140451 / 1000000000)) (hi := (39035113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584495189179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584495189179 / 500000000000) = 1/(500000000000 / 584495189179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_723 : Bounds (156140451 / 1000000000) (39035113 / 250000000) (Real.log (584495189179 / 500000000000)) := by
  have h := reflection_log_723_neg
  have he : Real.log (584495189179 / 500000000000) = -Real.log (500000000000 / 584495189179) := by
    rw [show ((584495189179 / 500000000000) : ℝ) = ((500000000000 / 584495189179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_724_neg : (156556987 / 1000000000) ≤ -Real.log (250000000000 / 292369351359) ∧
    -Real.log (250000000000 / 292369351359) ≤ (39139247 / 250000000) := by
  have h := checkLog_sound (w := (42369351359 / 542369351359)) (n := 12)
    (lo := (156556987 / 1000000000)) (hi := (39139247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292369351359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292369351359 / 250000000000) = 1/(250000000000 / 292369351359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_724 : Bounds (156556987 / 1000000000) (39139247 / 250000000) (Real.log (292369351359 / 250000000000)) := by
  have h := reflection_log_724_neg
  have he : Real.log (292369351359 / 250000000000) = -Real.log (250000000000 / 292369351359) := by
    rw [show ((292369351359 / 250000000000) : ℝ) = ((250000000000 / 292369351359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_725_neg : (156566897 / 500000000) ≤ -Real.log (250000000000 / 341926127619) ∧
    -Real.log (250000000000 / 341926127619) ≤ (62626759 / 200000000) := by
  have h := checkLog_sound (w := (91926127619 / 591926127619)) (n := 12)
    (lo := (156566897 / 500000000)) (hi := (62626759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341926127619 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341926127619 / 250000000000) = 1/(250000000000 / 341926127619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_725 : Bounds (156566897 / 500000000) (62626759 / 200000000) (Real.log (341926127619 / 250000000000)) := by
  have h := reflection_log_725_neg
  have he : Real.log (341926127619 / 250000000000) = -Real.log (250000000000 / 341926127619) := by
    rw [show ((341926127619 / 250000000000) : ℝ) = ((250000000000 / 341926127619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_726_neg : (15666937 / 50000000) ≤ -Real.log (500000000000 / 683992422449) ∧
    -Real.log (500000000000 / 683992422449) ≤ (313338741 / 1000000000) := by
  have h := checkLog_sound (w := (183992422449 / 1183992422449)) (n := 12)
    (lo := (15666937 / 50000000)) (hi := (313338741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683992422449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683992422449 / 500000000000) = 1/(500000000000 / 683992422449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_726 : Bounds (15666937 / 50000000) (313338741 / 1000000000) (Real.log (683992422449 / 500000000000)) := by
  have h := reflection_log_726_neg
  have he : Real.log (683992422449 / 500000000000) = -Real.log (500000000000 / 683992422449) := by
    rw [show ((683992422449 / 500000000000) : ℝ) = ((500000000000 / 683992422449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_727_neg : (2890663 / 20000000) ≤ -Real.log (2000 / 2311) ∧
    -Real.log (2000 / 2311) ≤ (144533151 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 4311)) (n := 12)
    (lo := (2890663 / 20000000)) (hi := (144533151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 2000) = 1/(2000 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_727 : Bounds (2890663 / 20000000) (144533151 / 1000000000) (Real.log (2311 / 2000)) := by
  have h := reflection_log_727_neg
  have he : Real.log (2311 / 2000) = -Real.log (2000 / 2311) := by
    rw [show ((2311 / 2000) : ℝ) = ((2000 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_728_neg : (84505271 / 500000000) ≤ -Real.log (1689 / 2000) ∧
    -Real.log (1689 / 2000) ≤ (169010543 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 3689)) (n := 12)
    (lo := (84505271 / 500000000)) (hi := (169010543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1689) = 1/(1689 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_728 : Bounds (-169010543 / 1000000000) (-84505271 / 500000000) (Real.log (1689 / 2000)) := by
  have h := reflection_log_728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_729_neg : (155487 / 1000000000) ≤ -Real.log (2000000 / 2000311) ∧
    -Real.log (2000000 / 2000311) ≤ (4859 / 31250000) := by
  have h := checkLog_sound (w := (311 / 4000311)) (n := 12)
    (lo := (155487 / 1000000000)) (hi := (4859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000311 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000311 / 2000000) = 1/(2000000 / 2000311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_729 : Bounds (155487 / 1000000000) (4859 / 31250000) (Real.log (2000311 / 2000000)) := by
  have h := reflection_log_729_neg
  have he : Real.log (2000311 / 2000000) = -Real.log (2000000 / 2000311) := by
    rw [show ((2000311 / 2000000) : ℝ) = ((2000000 / 2000311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_730_neg : (19439 / 125000000) ≤ -Real.log (1999689 / 2000000) ∧
    -Real.log (1999689 / 2000000) ≤ (155513 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 3999689)) (n := 12)
    (lo := (19439 / 125000000)) (hi := (155513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999689) = 1/(1999689 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_730 : Bounds (-155513 / 1000000000) (-19439 / 125000000) (Real.log (1999689 / 2000000)) := by
  have h := reflection_log_730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_731_neg : (75073149 / 1000000000) ≤ -Real.log (1000000 / 1077963) ∧
    -Real.log (1000000 / 1077963) ≤ (1501463 / 20000000) := by
  have h := checkLog_sound (w := (77963 / 2077963)) (n := 12)
    (lo := (75073149 / 1000000000)) (hi := (1501463 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077963 / 1000000) = 1/(1000000 / 1077963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_731 : Bounds (75073149 / 1000000000) (1501463 / 20000000) (Real.log (1077963 / 1000000)) := by
  have h := reflection_log_731_neg
  have he : Real.log (1077963 / 1000000) = -Real.log (1000000 / 1077963) := by
    rw [show ((1077963 / 1000000) : ℝ) = ((1000000 / 1077963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_732_neg : (40584963 / 500000000) ≤ -Real.log (922037 / 1000000) ∧
    -Real.log (922037 / 1000000) ≤ (81169927 / 1000000000) := by
  have h := checkLog_sound (w := (77963 / 1922037)) (n := 12)
    (lo := (40584963 / 500000000)) (hi := (81169927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922037) = 1/(922037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_732 : Bounds (-81169927 / 1000000000) (-40584963 / 500000000) (Real.log (922037 / 1000000)) := by
  have h := reflection_log_732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_733_neg : (75264231 / 1000000000) ≤ -Real.log (1000000 / 1078169) ∧
    -Real.log (1000000 / 1078169) ≤ (9408029 / 125000000) := by
  have h := checkLog_sound (w := (78169 / 2078169)) (n := 12)
    (lo := (75264231 / 1000000000)) (hi := (9408029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078169 / 1000000) = 1/(1000000 / 1078169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_733 : Bounds (75264231 / 1000000000) (9408029 / 125000000) (Real.log (1078169 / 1000000)) := by
  have h := reflection_log_733_neg
  have he : Real.log (1078169 / 1000000) = -Real.log (1000000 / 1078169) := by
    rw [show ((1078169 / 1000000) : ℝ) = ((1000000 / 1078169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_734_neg : (81393369 / 1000000000) ≤ -Real.log (921831 / 1000000) ∧
    -Real.log (921831 / 1000000) ≤ (8139337 / 100000000) := by
  have h := checkLog_sound (w := (78169 / 1921831)) (n := 12)
    (lo := (81393369 / 1000000000)) (hi := (8139337 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921831) = 1/(921831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_734 : Bounds (-8139337 / 100000000) (-81393369 / 1000000000) (Real.log (921831 / 1000000)) := by
  have h := reflection_log_734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_735_neg : (6129137 / 1000000000) ≤ -Real.log (993889607439 / 1000000000000) ∧
    -Real.log (993889607439 / 1000000000000) ≤ (3064569 / 500000000) := by
  have h := checkLog_sound (w := (6110392561 / 1993889607439)) (n := 12)
    (lo := (6129137 / 1000000000)) (hi := (3064569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993889607439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993889607439) = 1/(993889607439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_735 : Bounds (-3064569 / 500000000) (-6129137 / 1000000000) (Real.log (993889607439 / 1000000000000)) := by
  have h := reflection_log_735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_736_neg : (6096777 / 1000000000) ≤ -Real.log (993921770631 / 1000000000000) ∧
    -Real.log (993921770631 / 1000000000000) ≤ (3048389 / 500000000) := by
  have h := checkLog_sound (w := (6078229369 / 1993921770631)) (n := 12)
    (lo := (6096777 / 1000000000)) (hi := (3048389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993921770631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993921770631) = 1/(993921770631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_736 : Bounds (-3048389 / 500000000) (-6096777 / 1000000000) (Real.log (993921770631 / 1000000000000)) := by
  have h := reflection_log_736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_737_neg : (6249723 / 40000000) ≤ -Real.log (500000000000 / 584555175117) ∧
    -Real.log (500000000000 / 584555175117) ≤ (39060769 / 250000000) := by
  have h := checkLog_sound (w := (84555175117 / 1084555175117)) (n := 12)
    (lo := (6249723 / 40000000)) (hi := (39060769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584555175117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584555175117 / 500000000000) = 1/(500000000000 / 584555175117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_737 : Bounds (6249723 / 40000000) (39060769 / 250000000) (Real.log (584555175117 / 500000000000)) := by
  have h := reflection_log_737_neg
  have he : Real.log (584555175117 / 500000000000) = -Real.log (500000000000 / 584555175117) := by
    rw [show ((584555175117 / 500000000000) : ℝ) = ((500000000000 / 584555175117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_738_neg : (156657601 / 1000000000) ≤ -Real.log (125000000000 / 146199384703) ∧
    -Real.log (125000000000 / 146199384703) ≤ (78328801 / 500000000) := by
  have h := checkLog_sound (w := (21199384703 / 271199384703)) (n := 12)
    (lo := (156657601 / 1000000000)) (hi := (78328801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146199384703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146199384703 / 125000000000) = 1/(125000000000 / 146199384703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_738 : Bounds (156657601 / 1000000000) (78328801 / 500000000) (Real.log (146199384703 / 125000000000)) := by
  have h := reflection_log_738_neg
  have he : Real.log (146199384703 / 125000000000) = -Real.log (125000000000 / 146199384703) := by
    rw [show ((146199384703 / 125000000000) : ℝ) = ((125000000000 / 146199384703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_739_neg : (15666937 / 50000000) ≤ -Real.log (31250000000 / 42749526403) ∧
    -Real.log (31250000000 / 42749526403) ≤ (313338741 / 1000000000) := by
  have h := checkLog_sound (w := (11499526403 / 73999526403)) (n := 12)
    (lo := (15666937 / 50000000)) (hi := (313338741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42749526403 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42749526403 / 31250000000) = 1/(31250000000 / 42749526403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_739 : Bounds (15666937 / 50000000) (313338741 / 1000000000) (Real.log (42749526403 / 31250000000)) := by
  have h := reflection_log_739_neg
  have he : Real.log (42749526403 / 31250000000) = -Real.log (31250000000 / 42749526403) := by
    rw [show ((42749526403 / 31250000000) : ℝ) = ((31250000000 / 42749526403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_740_neg : (313543693 / 1000000000) ≤ -Real.log (250000000000 / 342066311427) ∧
    -Real.log (250000000000 / 342066311427) ≤ (156771847 / 500000000) := by
  have h := checkLog_sound (w := (92066311427 / 592066311427)) (n := 12)
    (lo := (313543693 / 1000000000)) (hi := (156771847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342066311427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342066311427 / 250000000000) = 1/(250000000000 / 342066311427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_740 : Bounds (313543693 / 1000000000) (156771847 / 500000000) (Real.log (342066311427 / 250000000000)) := by
  have h := reflection_log_740_neg
  have he : Real.log (342066311427 / 250000000000) = -Real.log (250000000000 / 342066311427) := by
    rw [show ((342066311427 / 250000000000) : ℝ) = ((250000000000 / 342066311427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_741_neg : (144619689 / 1000000000) ≤ -Real.log (2500 / 2889) ∧
    -Real.log (2500 / 2889) ≤ (14461969 / 100000000) := by
  have h := checkLog_sound (w := (389 / 5389)) (n := 12)
    (lo := (144619689 / 1000000000)) (hi := (14461969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 2500) = 1/(2500 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_741 : Bounds (144619689 / 1000000000) (14461969 / 100000000) (Real.log (2889 / 2500)) := by
  have h := reflection_log_741_neg
  have he : Real.log (2889 / 2500) = -Real.log (2500 / 2889) := by
    rw [show ((2889 / 2500) : ℝ) = ((2500 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_742_neg : (169128963 / 1000000000) ≤ -Real.log (2111 / 2500) ∧
    -Real.log (2111 / 2500) ≤ (42282241 / 250000000) := by
  have h := checkLog_sound (w := (389 / 4611)) (n := 12)
    (lo := (169128963 / 1000000000)) (hi := (42282241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2111) = 1/(2111 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_742 : Bounds (-42282241 / 250000000) (-169128963 / 1000000000) (Real.log (2111 / 2500)) := by
  have h := reflection_log_742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_743_neg : (155587 / 1000000000) ≤ -Real.log (2500000 / 2500389) ∧
    -Real.log (2500000 / 2500389) ≤ (38897 / 250000000) := by
  have h := checkLog_sound (w := (389 / 5000389)) (n := 12)
    (lo := (155587 / 1000000000)) (hi := (38897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500389 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500389 / 2500000) = 1/(2500000 / 2500389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_743 : Bounds (155587 / 1000000000) (38897 / 250000000) (Real.log (2500389 / 2500000)) := by
  have h := reflection_log_743_neg
  have he : Real.log (2500389 / 2500000) = -Real.log (2500000 / 2500389) := by
    rw [show ((2500389 / 2500000) : ℝ) = ((2500000 / 2500389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_744_neg : (38903 / 250000000) ≤ -Real.log (2499611 / 2500000) ∧
    -Real.log (2499611 / 2500000) ≤ (155613 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 4999611)) (n := 12)
    (lo := (38903 / 250000000)) (hi := (155613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499611) = 1/(2499611 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_744 : Bounds (-155613 / 1000000000) (-38903 / 250000000) (Real.log (2499611 / 2500000)) := by
  have h := reflection_log_744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_745_neg : (75120459 / 1000000000) ≤ -Real.log (500000 / 539007) ∧
    -Real.log (500000 / 539007) ≤ (3756023 / 50000000) := by
  have h := checkLog_sound (w := (39007 / 1039007)) (n := 12)
    (lo := (75120459 / 1000000000)) (hi := (3756023 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539007 / 500000) = 1/(500000 / 539007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_745 : Bounds (75120459 / 1000000000) (3756023 / 50000000) (Real.log (539007 / 500000)) := by
  have h := reflection_log_745_neg
  have he : Real.log (539007 / 500000) = -Real.log (500000 / 539007) := by
    rw [show ((539007 / 500000) : ℝ) = ((500000 / 539007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_746_neg : (81225239 / 1000000000) ≤ -Real.log (460993 / 500000) ∧
    -Real.log (460993 / 500000) ≤ (2030631 / 25000000) := by
  have h := checkLog_sound (w := (39007 / 960993)) (n := 12)
    (lo := (81225239 / 1000000000)) (hi := (2030631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460993) = 1/(460993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_746 : Bounds (-2030631 / 25000000) (-81225239 / 1000000000) (Real.log (460993 / 500000)) := by
  have h := reflection_log_746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_747_neg : (75311533 / 1000000000) ≤ -Real.log (50000 / 53911) ∧
    -Real.log (50000 / 53911) ≤ (37655767 / 500000000) := by
  have h := checkLog_sound (w := (3911 / 103911)) (n := 12)
    (lo := (75311533 / 1000000000)) (hi := (37655767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53911 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53911 / 50000) = 1/(50000 / 53911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_747 : Bounds (75311533 / 1000000000) (37655767 / 500000000) (Real.log (53911 / 50000)) := by
  have h := reflection_log_747_neg
  have he : Real.log (53911 / 50000) = -Real.log (50000 / 53911) := by
    rw [show ((53911 / 50000) : ℝ) = ((50000 / 53911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_748_neg : (16289739 / 200000000) ≤ -Real.log (46089 / 50000) ∧
    -Real.log (46089 / 50000) ≤ (10181087 / 125000000) := by
  have h := checkLog_sound (w := (3911 / 96089)) (n := 12)
    (lo := (16289739 / 200000000)) (hi := (10181087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 46089) = 1/(46089 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_748 : Bounds (-10181087 / 125000000) (-16289739 / 200000000) (Real.log (46089 / 50000)) := by
  have h := reflection_log_748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_749_neg : (3068581 / 500000000) ≤ -Real.log (2484704079 / 2500000000) ∧
    -Real.log (2484704079 / 2500000000) ≤ (6137163 / 1000000000) := by
  have h := checkLog_sound (w := (15295921 / 4984704079)) (n := 12)
    (lo := (3068581 / 500000000)) (hi := (6137163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2484704079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2484704079) = 1/(2484704079 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_749 : Bounds (-6137163 / 1000000000) (-3068581 / 500000000) (Real.log (2484704079 / 2500000000)) := by
  have h := reflection_log_749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_750_neg : (305239 / 50000000) ≤ -Real.log (248478453951 / 250000000000) ∧
    -Real.log (248478453951 / 250000000000) ≤ (6104781 / 1000000000) := by
  have h := checkLog_sound (w := (1521546049 / 498478453951)) (n := 12)
    (lo := (305239 / 50000000)) (hi := (6104781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248478453951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248478453951) = 1/(248478453951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_750 : Bounds (-6104781 / 1000000000) (-305239 / 50000000) (Real.log (248478453951 / 250000000000)) := by
  have h := reflection_log_750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_751_neg : (156345699 / 1000000000) ≤ -Real.log (125000000000 / 146153791923) ∧
    -Real.log (125000000000 / 146153791923) ≤ (1563457 / 10000000) := by
  have h := checkLog_sound (w := (21153791923 / 271153791923)) (n := 12)
    (lo := (156345699 / 1000000000)) (hi := (1563457 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146153791923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146153791923 / 125000000000) = 1/(125000000000 / 146153791923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_751 : Bounds (156345699 / 1000000000) (1563457 / 10000000) (Real.log (146153791923 / 125000000000)) := by
  have h := reflection_log_751_neg
  have he : Real.log (146153791923 / 125000000000) = -Real.log (125000000000 / 146153791923) := by
    rw [show ((146153791923 / 125000000000) : ℝ) = ((125000000000 / 146153791923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_752_neg : (39190057 / 250000000) ≤ -Real.log (500000000000 / 584857558203) ∧
    -Real.log (500000000000 / 584857558203) ≤ (156760229 / 1000000000) := by
  have h := checkLog_sound (w := (84857558203 / 1084857558203)) (n := 12)
    (lo := (39190057 / 250000000)) (hi := (156760229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584857558203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584857558203 / 500000000000) = 1/(500000000000 / 584857558203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_752 : Bounds (39190057 / 250000000) (156760229 / 1000000000) (Real.log (584857558203 / 500000000000)) := by
  have h := reflection_log_752_neg
  have he : Real.log (584857558203 / 500000000000) = -Real.log (500000000000 / 584857558203) := by
    rw [show ((584857558203 / 500000000000) : ℝ) = ((500000000000 / 584857558203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_753_neg : (313543693 / 1000000000) ≤ -Real.log (500000000000 / 684132622853) ∧
    -Real.log (500000000000 / 684132622853) ≤ (156771847 / 500000000) := by
  have h := checkLog_sound (w := (184132622853 / 1184132622853)) (n := 12)
    (lo := (313543693 / 1000000000)) (hi := (156771847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684132622853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684132622853 / 500000000000) = 1/(500000000000 / 684132622853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_753 : Bounds (313543693 / 1000000000) (156771847 / 500000000) (Real.log (684132622853 / 500000000000)) := by
  have h := reflection_log_753_neg
  have he : Real.log (684132622853 / 500000000000) = -Real.log (500000000000 / 684132622853) := by
    rw [show ((684132622853 / 500000000000) : ℝ) = ((500000000000 / 684132622853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_754_neg : (78437163 / 250000000) ≤ -Real.log (500000000000 / 684272856467) ∧
    -Real.log (500000000000 / 684272856467) ≤ (313748653 / 1000000000) := by
  have h := checkLog_sound (w := (184272856467 / 1184272856467)) (n := 12)
    (lo := (78437163 / 250000000)) (hi := (313748653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684272856467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684272856467 / 500000000000) = 1/(500000000000 / 684272856467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_754 : Bounds (78437163 / 250000000) (313748653 / 1000000000) (Real.log (684272856467 / 500000000000)) := by
  have h := reflection_log_754_neg
  have he : Real.log (684272856467 / 500000000000) = -Real.log (500000000000 / 684272856467) := by
    rw [show ((684272856467 / 500000000000) : ℝ) = ((500000000000 / 684272856467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_755_neg : (7235311 / 50000000) ≤ -Real.log (10000 / 11557) ∧
    -Real.log (10000 / 11557) ≤ (144706221 / 1000000000) := by
  have h := checkLog_sound (w := (1557 / 21557)) (n := 12)
    (lo := (7235311 / 50000000)) (hi := (144706221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11557 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11557 / 10000) = 1/(10000 / 11557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_755 : Bounds (7235311 / 50000000) (144706221 / 1000000000) (Real.log (11557 / 10000)) := by
  have h := reflection_log_755_neg
  have he : Real.log (11557 / 10000) = -Real.log (10000 / 11557) := by
    rw [show ((11557 / 10000) : ℝ) = ((10000 / 11557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_756_neg : (169247397 / 1000000000) ≤ -Real.log (8443 / 10000) ∧
    -Real.log (8443 / 10000) ≤ (84623699 / 500000000) := by
  have h := checkLog_sound (w := (1557 / 18443)) (n := 12)
    (lo := (169247397 / 1000000000)) (hi := (84623699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8443) = 1/(8443 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_756 : Bounds (-84623699 / 500000000) (-169247397 / 1000000000) (Real.log (8443 / 10000)) := by
  have h := reflection_log_756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_757_neg : (155687 / 1000000000) ≤ -Real.log (10000000 / 10001557) ∧
    -Real.log (10000000 / 10001557) ≤ (19461 / 125000000) := by
  have h := checkLog_sound (w := (1557 / 20001557)) (n := 12)
    (lo := (155687 / 1000000000)) (hi := (19461 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001557 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001557 / 10000000) = 1/(10000000 / 10001557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_757 : Bounds (155687 / 1000000000) (19461 / 125000000) (Real.log (10001557 / 10000000)) := by
  have h := reflection_log_757_neg
  have he : Real.log (10001557 / 10000000) = -Real.log (10000000 / 10001557) := by
    rw [show ((10001557 / 10000000) : ℝ) = ((10000000 / 10001557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_758_neg : (2433 / 15625000) ≤ -Real.log (9998443 / 10000000) ∧
    -Real.log (9998443 / 10000000) ≤ (155713 / 1000000000) := by
  have h := checkLog_sound (w := (1557 / 19998443)) (n := 12)
    (lo := (2433 / 15625000)) (hi := (155713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998443) = 1/(9998443 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_758 : Bounds (-155713 / 1000000000) (-2433 / 15625000) (Real.log (9998443 / 10000000)) := by
  have h := reflection_log_758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_759_neg : (75166839 / 1000000000) ≤ -Real.log (62500 / 67379) ∧
    -Real.log (62500 / 67379) ≤ (1879171 / 25000000) := by
  have h := checkLog_sound (w := (4879 / 129879)) (n := 12)
    (lo := (75166839 / 1000000000)) (hi := (1879171 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67379 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67379 / 62500) = 1/(62500 / 67379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_759 : Bounds (75166839 / 1000000000) (1879171 / 25000000) (Real.log (67379 / 62500)) := by
  have h := reflection_log_759_neg
  have he : Real.log (67379 / 62500) = -Real.log (62500 / 67379) := by
    rw [show ((67379 / 62500) : ℝ) = ((62500 / 67379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_760_neg : (5079967 / 62500000) ≤ -Real.log (57621 / 62500) ∧
    -Real.log (57621 / 62500) ≤ (81279473 / 1000000000) := by
  have h := checkLog_sound (w := (4879 / 120121)) (n := 12)
    (lo := (5079967 / 62500000)) (hi := (81279473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57621) = 1/(57621 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_760 : Bounds (-81279473 / 1000000000) (-5079967 / 62500000) (Real.log (57621 / 62500)) := by
  have h := reflection_log_760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_761_neg : (4709927 / 62500000) ≤ -Real.log (1000000 / 1078271) ∧
    -Real.log (1000000 / 1078271) ≤ (75358833 / 1000000000) := by
  have h := checkLog_sound (w := (78271 / 2078271)) (n := 12)
    (lo := (4709927 / 62500000)) (hi := (75358833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078271 / 1000000) = 1/(1000000 / 1078271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_761 : Bounds (4709927 / 62500000) (75358833 / 1000000000) (Real.log (1078271 / 1000000)) := by
  have h := reflection_log_761_neg
  have he : Real.log (1078271 / 1000000) = -Real.log (1000000 / 1078271) := by
    rw [show ((1078271 / 1000000) : ℝ) = ((1000000 / 1078271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_762_neg : (10188003 / 125000000) ≤ -Real.log (921729 / 1000000) ∧
    -Real.log (921729 / 1000000) ≤ (3260161 / 40000000) := by
  have h := checkLog_sound (w := (78271 / 1921729)) (n := 12)
    (lo := (10188003 / 125000000)) (hi := (3260161 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921729) = 1/(921729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_762 : Bounds (-3260161 / 40000000) (-10188003 / 125000000) (Real.log (921729 / 1000000)) := by
  have h := reflection_log_762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_763_neg : (768149 / 125000000) ≤ -Real.log (993873650559 / 1000000000000) ∧
    -Real.log (993873650559 / 1000000000000) ≤ (6145193 / 1000000000) := by
  have h := checkLog_sound (w := (6126349441 / 1993873650559)) (n := 12)
    (lo := (768149 / 125000000)) (hi := (6145193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993873650559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993873650559) = 1/(993873650559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_763 : Bounds (-6145193 / 1000000000) (-768149 / 125000000) (Real.log (993873650559 / 1000000000000)) := by
  have h := reflection_log_763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_764_neg : (764079 / 125000000) ≤ -Real.log (3882445359 / 3906250000) ∧
    -Real.log (3882445359 / 3906250000) ≤ (6112633 / 1000000000) := by
  have h := checkLog_sound (w := (23804641 / 7788695359)) (n := 12)
    (lo := (764079 / 125000000)) (hi := (6112633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3882445359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3882445359) = 1/(3882445359 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_764 : Bounds (-6112633 / 1000000000) (-764079 / 125000000) (Real.log (3882445359 / 3906250000)) := by
  have h := reflection_log_764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_765_neg : (19555789 / 125000000) ≤ -Real.log (100000000000 / 116934798077) ∧
    -Real.log (100000000000 / 116934798077) ≤ (156446313 / 1000000000) := by
  have h := checkLog_sound (w := (16934798077 / 216934798077)) (n := 12)
    (lo := (19555789 / 125000000)) (hi := (156446313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116934798077 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116934798077 / 100000000000) = 1/(100000000000 / 116934798077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_765 : Bounds (19555789 / 125000000) (156446313 / 1000000000) (Real.log (116934798077 / 100000000000)) := by
  have h := reflection_log_765_neg
  have he : Real.log (116934798077 / 100000000000) = -Real.log (100000000000 / 116934798077) := by
    rw [show ((116934798077 / 100000000000) : ℝ) = ((100000000000 / 116934798077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_766_neg : (156862857 / 1000000000) ≤ -Real.log (125000000000 / 146229396059) ∧
    -Real.log (125000000000 / 146229396059) ≤ (78431429 / 500000000) := by
  have h := checkLog_sound (w := (21229396059 / 271229396059)) (n := 12)
    (lo := (156862857 / 1000000000)) (hi := (78431429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146229396059 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146229396059 / 125000000000) = 1/(125000000000 / 146229396059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_766 : Bounds (156862857 / 1000000000) (78431429 / 500000000) (Real.log (146229396059 / 125000000000)) := by
  have h := reflection_log_766_neg
  have he : Real.log (146229396059 / 125000000000) = -Real.log (125000000000 / 146229396059) := by
    rw [show ((146229396059 / 125000000000) : ℝ) = ((125000000000 / 146229396059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_767_neg : (78437163 / 250000000) ≤ -Real.log (250000000000 / 342136428233) ∧
    -Real.log (250000000000 / 342136428233) ≤ (313748653 / 1000000000) := by
  have h := checkLog_sound (w := (92136428233 / 592136428233)) (n := 12)
    (lo := (78437163 / 250000000)) (hi := (313748653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342136428233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342136428233 / 250000000000) = 1/(250000000000 / 342136428233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_767 : Bounds (78437163 / 250000000) (313748653 / 1000000000) (Real.log (342136428233 / 250000000000)) := by
  have h := reflection_log_767_neg
  have he : Real.log (342136428233 / 250000000000) = -Real.log (250000000000 / 342136428233) := by
    rw [show ((342136428233 / 250000000000) : ℝ) = ((250000000000 / 342136428233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0012 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_768_neg : (156976809 / 500000000) ≤ -Real.log (250000000000 / 342206561649) ∧
    -Real.log (250000000000 / 342206561649) ≤ (313953619 / 1000000000) := by
  have h := checkLog_sound (w := (92206561649 / 592206561649)) (n := 12)
    (lo := (156976809 / 500000000)) (hi := (313953619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342206561649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342206561649 / 250000000000) = 1/(250000000000 / 342206561649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_768 : Bounds (156976809 / 500000000) (313953619 / 1000000000) (Real.log (342206561649 / 250000000000)) := by
  have h := reflection_log_768_neg
  have he : Real.log (342206561649 / 250000000000) = -Real.log (250000000000 / 342206561649) := by
    rw [show ((342206561649 / 250000000000) : ℝ) = ((250000000000 / 342206561649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_769_neg : (18099093 / 125000000) ≤ -Real.log (5000 / 5779) ∧
    -Real.log (5000 / 5779) ≤ (28958549 / 200000000) := by
  have h := checkLog_sound (w := (779 / 10779)) (n := 12)
    (lo := (18099093 / 125000000)) (hi := (28958549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5779 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5779 / 5000) = 1/(5000 / 5779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_769 : Bounds (18099093 / 125000000) (28958549 / 200000000) (Real.log (5779 / 5000)) := by
  have h := reflection_log_769_neg
  have he : Real.log (5779 / 5000) = -Real.log (5000 / 5779) := by
    rw [show ((5779 / 5000) : ℝ) = ((5000 / 5779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_770_neg : (33873169 / 200000000) ≤ -Real.log (4221 / 5000) ∧
    -Real.log (4221 / 5000) ≤ (84682923 / 500000000) := by
  have h := checkLog_sound (w := (779 / 9221)) (n := 12)
    (lo := (33873169 / 200000000)) (hi := (84682923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4221) = 1/(4221 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_770 : Bounds (-84682923 / 500000000) (-33873169 / 200000000) (Real.log (4221 / 5000)) := by
  have h := reflection_log_770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_771_neg : (155787 / 1000000000) ≤ -Real.log (5000000 / 5000779) ∧
    -Real.log (5000000 / 5000779) ≤ (38947 / 250000000) := by
  have h := checkLog_sound (w := (779 / 10000779)) (n := 12)
    (lo := (155787 / 1000000000)) (hi := (38947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000779 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000779 / 5000000) = 1/(5000000 / 5000779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_771 : Bounds (155787 / 1000000000) (38947 / 250000000) (Real.log (5000779 / 5000000)) := by
  have h := reflection_log_771_neg
  have he : Real.log (5000779 / 5000000) = -Real.log (5000000 / 5000779) := by
    rw [show ((5000779 / 5000000) : ℝ) = ((5000000 / 5000779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_772_neg : (38953 / 250000000) ≤ -Real.log (4999221 / 5000000) ∧
    -Real.log (4999221 / 5000000) ≤ (155813 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 9999221)) (n := 12)
    (lo := (38953 / 250000000)) (hi := (155813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999221) = 1/(4999221 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_772 : Bounds (-155813 / 1000000000) (-38953 / 250000000) (Real.log (4999221 / 5000000)) := by
  have h := reflection_log_772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_773_neg : (15042829 / 200000000) ≤ -Real.log (200000 / 215623) ∧
    -Real.log (200000 / 215623) ≤ (37607073 / 500000000) := by
  have h := checkLog_sound (w := (15623 / 415623)) (n := 12)
    (lo := (15042829 / 200000000)) (hi := (37607073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215623 / 200000) = 1/(200000 / 215623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_773 : Bounds (15042829 / 200000000) (37607073 / 500000000) (Real.log (215623 / 200000)) := by
  have h := reflection_log_773_neg
  have he : Real.log (215623 / 200000) = -Real.log (200000 / 215623) := by
    rw [show ((215623 / 200000) : ℝ) = ((200000 / 215623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_774_neg : (10166849 / 125000000) ≤ -Real.log (184377 / 200000) ∧
    -Real.log (184377 / 200000) ≤ (81334793 / 1000000000) := by
  have h := checkLog_sound (w := (15623 / 384377)) (n := 12)
    (lo := (10166849 / 125000000)) (hi := (81334793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184377) = 1/(184377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_774 : Bounds (-81334793 / 1000000000) (-10166849 / 125000000) (Real.log (184377 / 200000)) := by
  have h := reflection_log_774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_775_neg : (75405201 / 1000000000) ≤ -Real.log (1000000 / 1078321) ∧
    -Real.log (1000000 / 1078321) ≤ (37702601 / 500000000) := by
  have h := checkLog_sound (w := (78321 / 2078321)) (n := 12)
    (lo := (75405201 / 1000000000)) (hi := (37702601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078321 / 1000000) = 1/(1000000 / 1078321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_775 : Bounds (75405201 / 1000000000) (37702601 / 500000000) (Real.log (1078321 / 1000000)) := by
  have h := reflection_log_775_neg
  have he : Real.log (1078321 / 1000000) = -Real.log (1000000 / 1078321) := by
    rw [show ((1078321 / 1000000) : ℝ) = ((1000000 / 1078321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_776_neg : (318587 / 3906250) ≤ -Real.log (921679 / 1000000) ∧
    -Real.log (921679 / 1000000) ≤ (81558273 / 1000000000) := by
  have h := checkLog_sound (w := (78321 / 1921679)) (n := 12)
    (lo := (318587 / 3906250)) (hi := (81558273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921679) = 1/(921679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_776 : Bounds (-81558273 / 1000000000) (-318587 / 3906250) (Real.log (921679 / 1000000)) := by
  have h := reflection_log_776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_777_neg : (615307 / 100000000) ≤ -Real.log (993865820959 / 1000000000000) ∧
    -Real.log (993865820959 / 1000000000000) ≤ (6153071 / 1000000000) := by
  have h := checkLog_sound (w := (6134179041 / 1993865820959)) (n := 12)
    (lo := (615307 / 100000000)) (hi := (6153071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993865820959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993865820959) = 1/(993865820959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_777 : Bounds (-6153071 / 1000000000) (-615307 / 100000000) (Real.log (993865820959 / 1000000000000)) := by
  have h := reflection_log_777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_778_neg : (3060323 / 500000000) ≤ -Real.log (39755921871 / 40000000000) ∧
    -Real.log (39755921871 / 40000000000) ≤ (6120647 / 1000000000) := by
  have h := checkLog_sound (w := (244078129 / 79755921871)) (n := 12)
    (lo := (3060323 / 500000000)) (hi := (6120647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39755921871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39755921871) = 1/(39755921871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_778 : Bounds (-6120647 / 1000000000) (-3060323 / 500000000) (Real.log (39755921871 / 40000000000)) := by
  have h := reflection_log_778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_779_neg : (156548937 / 1000000000) ≤ -Real.log (100000000000 / 116946799221) ∧
    -Real.log (100000000000 / 116946799221) ≤ (78274469 / 500000000) := by
  have h := checkLog_sound (w := (16946799221 / 216946799221)) (n := 12)
    (lo := (156548937 / 1000000000)) (hi := (78274469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116946799221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116946799221 / 100000000000) = 1/(100000000000 / 116946799221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_779 : Bounds (156548937 / 1000000000) (78274469 / 500000000) (Real.log (116946799221 / 100000000000)) := by
  have h := reflection_log_779_neg
  have he : Real.log (116946799221 / 100000000000) = -Real.log (100000000000 / 116946799221) := by
    rw [show ((116946799221 / 100000000000) : ℝ) = ((100000000000 / 116946799221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_780_neg : (78481737 / 500000000) ≤ -Real.log (500000000000 / 584976439737) ∧
    -Real.log (500000000000 / 584976439737) ≤ (6278539 / 40000000) := by
  have h := checkLog_sound (w := (84976439737 / 1084976439737)) (n := 12)
    (lo := (78481737 / 500000000)) (hi := (6278539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584976439737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584976439737 / 500000000000) = 1/(500000000000 / 584976439737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_780 : Bounds (78481737 / 500000000) (6278539 / 40000000) (Real.log (584976439737 / 500000000000)) := by
  have h := reflection_log_780_neg
  have he : Real.log (584976439737 / 500000000000) = -Real.log (500000000000 / 584976439737) := by
    rw [show ((584976439737 / 500000000000) : ℝ) = ((500000000000 / 584976439737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_781_neg : (156976809 / 500000000) ≤ -Real.log (500000000000 / 684413123297) ∧
    -Real.log (500000000000 / 684413123297) ≤ (313953619 / 1000000000) := by
  have h := checkLog_sound (w := (184413123297 / 1184413123297)) (n := 12)
    (lo := (156976809 / 500000000)) (hi := (313953619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684413123297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684413123297 / 500000000000) = 1/(500000000000 / 684413123297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_781 : Bounds (156976809 / 500000000) (313953619 / 1000000000) (Real.log (684413123297 / 500000000000)) := by
  have h := reflection_log_781_neg
  have he : Real.log (684413123297 / 500000000000) = -Real.log (500000000000 / 684413123297) := by
    rw [show ((684413123297 / 500000000000) : ℝ) = ((500000000000 / 684413123297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_782_neg : (31415859 / 100000000) ≤ -Real.log (195312500 / 267403681) ∧
    -Real.log (195312500 / 267403681) ≤ (314158591 / 1000000000) := by
  have h := checkLog_sound (w := (72091181 / 462716181)) (n := 12)
    (lo := (31415859 / 100000000)) (hi := (314158591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267403681 / 195312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267403681 / 195312500) = 1/(195312500 / 267403681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_782 : Bounds (31415859 / 100000000) (314158591 / 1000000000) (Real.log (267403681 / 195312500)) := by
  have h := reflection_log_782_neg
  have he : Real.log (267403681 / 195312500) = -Real.log (195312500 / 267403681) := by
    rw [show ((267403681 / 195312500) : ℝ) = ((195312500 / 267403681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_783_neg : (144879261 / 1000000000) ≤ -Real.log (10000 / 11559) ∧
    -Real.log (10000 / 11559) ≤ (72439631 / 500000000) := by
  have h := checkLog_sound (w := (1559 / 21559)) (n := 12)
    (lo := (144879261 / 1000000000)) (hi := (72439631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11559 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11559 / 10000) = 1/(10000 / 11559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_783 : Bounds (144879261 / 1000000000) (72439631 / 500000000) (Real.log (11559 / 10000)) := by
  have h := reflection_log_783_neg
  have he : Real.log (11559 / 10000) = -Real.log (10000 / 11559) := by
    rw [show ((11559 / 10000) : ℝ) = ((10000 / 11559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_784_neg : (169484307 / 1000000000) ≤ -Real.log (8441 / 10000) ∧
    -Real.log (8441 / 10000) ≤ (42371077 / 250000000) := by
  have h := checkLog_sound (w := (1559 / 18441)) (n := 12)
    (lo := (169484307 / 1000000000)) (hi := (42371077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8441) = 1/(8441 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_784 : Bounds (-42371077 / 250000000) (-169484307 / 1000000000) (Real.log (8441 / 10000)) := by
  have h := reflection_log_784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_785_neg : (155887 / 1000000000) ≤ -Real.log (10000000 / 10001559) ∧
    -Real.log (10000000 / 10001559) ≤ (9743 / 62500000) := by
  have h := checkLog_sound (w := (1559 / 20001559)) (n := 12)
    (lo := (155887 / 1000000000)) (hi := (9743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001559 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001559 / 10000000) = 1/(10000000 / 10001559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_785 : Bounds (155887 / 1000000000) (9743 / 62500000) (Real.log (10001559 / 10000000)) := by
  have h := reflection_log_785_neg
  have he : Real.log (10001559 / 10000000) = -Real.log (10000000 / 10001559) := by
    rw [show ((10001559 / 10000000) : ℝ) = ((10000000 / 10001559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_786_neg : (19489 / 125000000) ≤ -Real.log (9998441 / 10000000) ∧
    -Real.log (9998441 / 10000000) ≤ (155913 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 19998441)) (n := 12)
    (lo := (19489 / 125000000)) (hi := (155913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998441) = 1/(9998441 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_786 : Bounds (-155913 / 1000000000) (-19489 / 125000000) (Real.log (9998441 / 10000000)) := by
  have h := reflection_log_786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_787_neg : (75260521 / 1000000000) ≤ -Real.log (200000 / 215633) ∧
    -Real.log (200000 / 215633) ≤ (37630261 / 500000000) := by
  have h := checkLog_sound (w := (15633 / 415633)) (n := 12)
    (lo := (75260521 / 1000000000)) (hi := (37630261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215633 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215633 / 200000) = 1/(200000 / 215633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_787 : Bounds (75260521 / 1000000000) (37630261 / 500000000) (Real.log (215633 / 200000)) := by
  have h := reflection_log_787_neg
  have he : Real.log (215633 / 200000) = -Real.log (200000 / 215633) := by
    rw [show ((215633 / 200000) : ℝ) = ((200000 / 215633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_788_neg : (8138903 / 100000000) ≤ -Real.log (184367 / 200000) ∧
    -Real.log (184367 / 200000) ≤ (81389031 / 1000000000) := by
  have h := checkLog_sound (w := (15633 / 384367)) (n := 12)
    (lo := (8138903 / 100000000)) (hi := (81389031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184367) = 1/(184367 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_788 : Bounds (-81389031 / 1000000000) (-8138903 / 100000000) (Real.log (184367 / 200000)) := by
  have h := reflection_log_788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_789_neg : (4715781 / 62500000) ≤ -Real.log (250000 / 269593) ∧
    -Real.log (250000 / 269593) ≤ (75452497 / 1000000000) := by
  have h := checkLog_sound (w := (19593 / 519593)) (n := 12)
    (lo := (4715781 / 62500000)) (hi := (75452497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269593 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269593 / 250000) = 1/(250000 / 269593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_789 : Bounds (4715781 / 62500000) (75452497 / 1000000000) (Real.log (269593 / 250000)) := by
  have h := reflection_log_789_neg
  have he : Real.log (269593 / 250000) = -Real.log (250000 / 269593) := by
    rw [show ((269593 / 250000) : ℝ) = ((250000 / 269593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_790_neg : (81613607 / 1000000000) ≤ -Real.log (230407 / 250000) ∧
    -Real.log (230407 / 250000) ≤ (10201701 / 125000000) := by
  have h := checkLog_sound (w := (19593 / 480407)) (n := 12)
    (lo := (81613607 / 1000000000)) (hi := (10201701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230407) = 1/(230407 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_790 : Bounds (-10201701 / 125000000) (-81613607 / 1000000000) (Real.log (230407 / 250000)) := by
  have h := reflection_log_790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_791_neg : (6161111 / 1000000000) ≤ -Real.log (62116114351 / 62500000000) ∧
    -Real.log (62116114351 / 62500000000) ≤ (770139 / 125000000) := by
  have h := checkLog_sound (w := (383885649 / 124616114351)) (n := 12)
    (lo := (6161111 / 1000000000)) (hi := (770139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62116114351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62116114351) = 1/(62116114351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_791 : Bounds (-770139 / 125000000) (-6161111 / 1000000000) (Real.log (62116114351 / 62500000000)) := by
  have h := reflection_log_791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_792_neg : (1532127 / 250000000) ≤ -Real.log (39755609311 / 40000000000) ∧
    -Real.log (39755609311 / 40000000000) ≤ (6128509 / 1000000000) := by
  have h := checkLog_sound (w := (244390689 / 79755609311)) (n := 12)
    (lo := (1532127 / 250000000)) (hi := (6128509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39755609311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39755609311) = 1/(39755609311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_792 : Bounds (-6128509 / 1000000000) (-1532127 / 250000000) (Real.log (39755609311 / 40000000000)) := by
  have h := reflection_log_792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_793_neg : (9790597 / 62500000) ≤ -Real.log (62500000000 / 73099103961) ∧
    -Real.log (62500000000 / 73099103961) ≤ (156649553 / 1000000000) := by
  have h := checkLog_sound (w := (10599103961 / 135599103961)) (n := 12)
    (lo := (9790597 / 62500000)) (hi := (156649553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73099103961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73099103961 / 62500000000) = 1/(62500000000 / 73099103961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_793 : Bounds (9790597 / 62500000) (156649553 / 1000000000) (Real.log (73099103961 / 62500000000)) := by
  have h := reflection_log_793_neg
  have he : Real.log (73099103961 / 62500000000) = -Real.log (62500000000 / 73099103961) := by
    rw [show ((73099103961 / 62500000000) : ℝ) = ((62500000000 / 73099103961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_794_neg : (19633263 / 125000000) ≤ -Real.log (500000000000 / 585036478927) ∧
    -Real.log (500000000000 / 585036478927) ≤ (31413221 / 200000000) := by
  have h := checkLog_sound (w := (85036478927 / 1085036478927)) (n := 12)
    (lo := (19633263 / 125000000)) (hi := (31413221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585036478927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585036478927 / 500000000000) = 1/(500000000000 / 585036478927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_794 : Bounds (19633263 / 125000000) (31413221 / 200000000) (Real.log (585036478927 / 500000000000)) := by
  have h := reflection_log_794_neg
  have he : Real.log (585036478927 / 500000000000) = -Real.log (500000000000 / 585036478927) := by
    rw [show ((585036478927 / 500000000000) : ℝ) = ((500000000000 / 585036478927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_795_neg : (31415859 / 100000000) ≤ -Real.log (500000000000 / 684553423359) ∧
    -Real.log (500000000000 / 684553423359) ≤ (314158591 / 1000000000) := by
  have h := checkLog_sound (w := (184553423359 / 1184553423359)) (n := 12)
    (lo := (31415859 / 100000000)) (hi := (314158591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684553423359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684553423359 / 500000000000) = 1/(500000000000 / 684553423359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_795 : Bounds (31415859 / 100000000) (314158591 / 1000000000) (Real.log (684553423359 / 500000000000)) := by
  have h := reflection_log_795_neg
  have he : Real.log (684553423359 / 500000000000) = -Real.log (500000000000 / 684553423359) := by
    rw [show ((684553423359 / 500000000000) : ℝ) = ((500000000000 / 684553423359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_796_neg : (314363569 / 1000000000) ≤ -Real.log (62500000000 / 85586719583) ∧
    -Real.log (62500000000 / 85586719583) ≤ (31436357 / 100000000) := by
  have h := checkLog_sound (w := (23086719583 / 148086719583)) (n := 12)
    (lo := (314363569 / 1000000000)) (hi := (31436357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85586719583 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85586719583 / 62500000000) = 1/(62500000000 / 85586719583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_796 : Bounds (314363569 / 1000000000) (31436357 / 100000000) (Real.log (85586719583 / 62500000000)) := by
  have h := reflection_log_796_neg
  have he : Real.log (85586719583 / 62500000000) = -Real.log (62500000000 / 85586719583) := by
    rw [show ((85586719583 / 62500000000) : ℝ) = ((62500000000 / 85586719583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_797_neg : (14496577 / 100000000) ≤ -Real.log (250 / 289) ∧
    -Real.log (250 / 289) ≤ (144965771 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 539)) (n := 12)
    (lo := (14496577 / 100000000)) (hi := (144965771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289 / 250) = 1/(250 / 289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_797 : Bounds (14496577 / 100000000) (144965771 / 1000000000) (Real.log (289 / 250)) := by
  have h := reflection_log_797_neg
  have he : Real.log (289 / 250) = -Real.log (250 / 289) := by
    rw [show ((289 / 250) : ℝ) = ((250 / 289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_798_neg : (5300087 / 31250000) ≤ -Real.log (211 / 250) ∧
    -Real.log (211 / 250) ≤ (33920557 / 200000000) := by
  have h := checkLog_sound (w := (39 / 461)) (n := 12)
    (lo := (5300087 / 31250000)) (hi := (33920557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 211) = 1/(211 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_798 : Bounds (-33920557 / 200000000) (-5300087 / 31250000) (Real.log (211 / 250)) := by
  have h := reflection_log_798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_799_neg : (155987 / 1000000000) ≤ -Real.log (250000 / 250039) ∧
    -Real.log (250000 / 250039) ≤ (38997 / 250000000) := by
  have h := checkLog_sound (w := (39 / 500039)) (n := 12)
    (lo := (155987 / 1000000000)) (hi := (38997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250039 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250039 / 250000) = 1/(250000 / 250039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_799 : Bounds (155987 / 1000000000) (38997 / 250000000) (Real.log (250039 / 250000)) := by
  have h := reflection_log_799_neg
  have he : Real.log (250039 / 250000) = -Real.log (250000 / 250039) := by
    rw [show ((250039 / 250000) : ℝ) = ((250000 / 250039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_800_neg : (39003 / 250000000) ≤ -Real.log (249961 / 250000) ∧
    -Real.log (249961 / 250000) ≤ (156013 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 499961)) (n := 12)
    (lo := (39003 / 250000000)) (hi := (156013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249961) = 1/(249961 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_800 : Bounds (-156013 / 1000000000) (-39003 / 250000000) (Real.log (249961 / 250000)) := by
  have h := reflection_log_800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_801_neg : (75307823 / 1000000000) ≤ -Real.log (125000 / 134777) ∧
    -Real.log (125000 / 134777) ≤ (4706739 / 62500000) := by
  have h := checkLog_sound (w := (9777 / 259777)) (n := 12)
    (lo := (75307823 / 1000000000)) (hi := (4706739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134777 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134777 / 125000) = 1/(125000 / 134777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_801 : Bounds (75307823 / 1000000000) (4706739 / 62500000) (Real.log (134777 / 125000)) := by
  have h := reflection_log_801_neg
  have he : Real.log (134777 / 125000) = -Real.log (125000 / 134777) := by
    rw [show ((134777 / 125000) : ℝ) = ((125000 / 134777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_802_neg : (20361089 / 250000000) ≤ -Real.log (115223 / 125000) ∧
    -Real.log (115223 / 125000) ≤ (81444357 / 1000000000) := by
  have h := checkLog_sound (w := (9777 / 240223)) (n := 12)
    (lo := (20361089 / 250000000)) (hi := (81444357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115223) = 1/(115223 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_802 : Bounds (-81444357 / 1000000000) (-20361089 / 250000000) (Real.log (115223 / 125000)) := by
  have h := reflection_log_802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_803_neg : (18874947 / 250000000) ≤ -Real.log (1000000 / 1078423) ∧
    -Real.log (1000000 / 1078423) ≤ (75499789 / 1000000000) := by
  have h := checkLog_sound (w := (78423 / 2078423)) (n := 12)
    (lo := (18874947 / 250000000)) (hi := (75499789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078423 / 1000000) = 1/(1000000 / 1078423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_803 : Bounds (18874947 / 250000000) (75499789 / 1000000000) (Real.log (1078423 / 1000000)) := by
  have h := reflection_log_803_neg
  have he : Real.log (1078423 / 1000000) = -Real.log (1000000 / 1078423) := by
    rw [show ((1078423 / 1000000) : ℝ) = ((1000000 / 1078423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_804_neg : (16333789 / 200000000) ≤ -Real.log (921577 / 1000000) ∧
    -Real.log (921577 / 1000000) ≤ (40834473 / 500000000) := by
  have h := checkLog_sound (w := (78423 / 1921577)) (n := 12)
    (lo := (16333789 / 200000000)) (hi := (40834473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921577) = 1/(921577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_804 : Bounds (-40834473 / 500000000) (-16333789 / 200000000) (Real.log (921577 / 1000000)) := by
  have h := reflection_log_804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_805_neg : (6169157 / 1000000000) ≤ -Real.log (993849833071 / 1000000000000) ∧
    -Real.log (993849833071 / 1000000000000) ≤ (3084579 / 500000000) := by
  have h := checkLog_sound (w := (6150166929 / 1993849833071)) (n := 12)
    (lo := (6169157 / 1000000000)) (hi := (3084579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993849833071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993849833071) = 1/(993849833071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_805 : Bounds (-3084579 / 500000000) (-6169157 / 1000000000) (Real.log (993849833071 / 1000000000000)) := by
  have h := reflection_log_805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_806_neg : (1534133 / 250000000) ≤ -Real.log (15529410271 / 15625000000) ∧
    -Real.log (15529410271 / 15625000000) ≤ (6136533 / 1000000000) := by
  have h := checkLog_sound (w := (95589729 / 31154410271)) (n := 12)
    (lo := (1534133 / 250000000)) (hi := (6136533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15529410271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15529410271) = 1/(15529410271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_806 : Bounds (-6136533 / 1000000000) (-1534133 / 250000000) (Real.log (15529410271 / 15625000000)) := by
  have h := reflection_log_806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_807_neg : (156752179 / 1000000000) ≤ -Real.log (500000000000 / 584852850559) ∧
    -Real.log (500000000000 / 584852850559) ≤ (7837609 / 50000000) := by
  have h := checkLog_sound (w := (84852850559 / 1084852850559)) (n := 12)
    (lo := (156752179 / 1000000000)) (hi := (7837609 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584852850559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584852850559 / 500000000000) = 1/(500000000000 / 584852850559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_807 : Bounds (156752179 / 1000000000) (7837609 / 50000000) (Real.log (584852850559 / 500000000000)) := by
  have h := reflection_log_807_neg
  have he : Real.log (584852850559 / 500000000000) = -Real.log (500000000000 / 584852850559) := by
    rw [show ((584852850559 / 500000000000) : ℝ) = ((500000000000 / 584852850559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_808_neg : (78584367 / 500000000) ≤ -Real.log (250000000000 / 292548262381) ∧
    -Real.log (250000000000 / 292548262381) ≤ (31433747 / 200000000) := by
  have h := checkLog_sound (w := (42548262381 / 542548262381)) (n := 12)
    (lo := (78584367 / 500000000)) (hi := (31433747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292548262381 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292548262381 / 250000000000) = 1/(250000000000 / 292548262381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_808 : Bounds (78584367 / 500000000) (31433747 / 200000000) (Real.log (292548262381 / 250000000000)) := by
  have h := reflection_log_808_neg
  have he : Real.log (292548262381 / 250000000000) = -Real.log (250000000000 / 292548262381) := by
    rw [show ((292548262381 / 250000000000) : ℝ) = ((250000000000 / 292548262381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_809_neg : (314363569 / 1000000000) ≤ -Real.log (500000000000 / 684693756663) ∧
    -Real.log (500000000000 / 684693756663) ≤ (31436357 / 100000000) := by
  have h := checkLog_sound (w := (184693756663 / 1184693756663)) (n := 12)
    (lo := (314363569 / 1000000000)) (hi := (31436357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684693756663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684693756663 / 500000000000) = 1/(500000000000 / 684693756663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_809 : Bounds (314363569 / 1000000000) (31436357 / 100000000) (Real.log (684693756663 / 500000000000)) := by
  have h := reflection_log_809_neg
  have he : Real.log (684693756663 / 500000000000) = -Real.log (500000000000 / 684693756663) := by
    rw [show ((684693756663 / 500000000000) : ℝ) = ((500000000000 / 684693756663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_810_neg : (157284277 / 500000000) ≤ -Real.log (500000000000 / 684834123223) ∧
    -Real.log (500000000000 / 684834123223) ≤ (62913711 / 200000000) := by
  have h := checkLog_sound (w := (184834123223 / 1184834123223)) (n := 12)
    (lo := (157284277 / 500000000)) (hi := (62913711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684834123223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684834123223 / 500000000000) = 1/(500000000000 / 684834123223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_810 : Bounds (157284277 / 500000000) (62913711 / 200000000) (Real.log (684834123223 / 500000000000)) := by
  have h := reflection_log_810_neg
  have he : Real.log (684834123223 / 500000000000) = -Real.log (500000000000 / 684834123223) := by
    rw [show ((684834123223 / 500000000000) : ℝ) = ((500000000000 / 684834123223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_811_neg : (145052271 / 1000000000) ≤ -Real.log (10000 / 11561) ∧
    -Real.log (10000 / 11561) ≤ (9065767 / 62500000) := by
  have h := checkLog_sound (w := (1561 / 21561)) (n := 12)
    (lo := (145052271 / 1000000000)) (hi := (9065767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11561 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11561 / 10000) = 1/(10000 / 11561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_811 : Bounds (145052271 / 1000000000) (9065767 / 62500000) (Real.log (11561 / 10000)) := by
  have h := reflection_log_811_neg
  have he : Real.log (11561 / 10000) = -Real.log (10000 / 11561) := by
    rw [show ((11561 / 10000) : ℝ) = ((10000 / 11561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_812_neg : (84860637 / 500000000) ≤ -Real.log (8439 / 10000) ∧
    -Real.log (8439 / 10000) ≤ (6788851 / 40000000) := by
  have h := checkLog_sound (w := (1561 / 18439)) (n := 12)
    (lo := (84860637 / 500000000)) (hi := (6788851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8439) = 1/(8439 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_812 : Bounds (-6788851 / 40000000) (-84860637 / 500000000) (Real.log (8439 / 10000)) := by
  have h := reflection_log_812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_813_neg : (156087 / 1000000000) ≤ -Real.log (10000000 / 10001561) ∧
    -Real.log (10000000 / 10001561) ≤ (19511 / 125000000) := by
  have h := checkLog_sound (w := (1561 / 20001561)) (n := 12)
    (lo := (156087 / 1000000000)) (hi := (19511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001561 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001561 / 10000000) = 1/(10000000 / 10001561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_813 : Bounds (156087 / 1000000000) (19511 / 125000000) (Real.log (10001561 / 10000000)) := by
  have h := reflection_log_813_neg
  have he : Real.log (10001561 / 10000000) = -Real.log (10000000 / 10001561) := by
    rw [show ((10001561 / 10000000) : ℝ) = ((10000000 / 10001561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_814_neg : (9757 / 62500000) ≤ -Real.log (9998439 / 10000000) ∧
    -Real.log (9998439 / 10000000) ≤ (156113 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 19998439)) (n := 12)
    (lo := (9757 / 62500000)) (hi := (156113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998439) = 1/(9998439 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_814 : Bounds (-156113 / 1000000000) (-9757 / 62500000) (Real.log (9998439 / 10000000)) := by
  have h := reflection_log_814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_815_neg : (37677561 / 500000000) ≤ -Real.log (1000000 / 1078267) ∧
    -Real.log (1000000 / 1078267) ≤ (75355123 / 1000000000) := by
  have h := checkLog_sound (w := (78267 / 2078267)) (n := 12)
    (lo := (37677561 / 500000000)) (hi := (75355123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078267 / 1000000) = 1/(1000000 / 1078267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_815 : Bounds (37677561 / 500000000) (75355123 / 1000000000) (Real.log (1078267 / 1000000)) := by
  have h := reflection_log_815_neg
  have he : Real.log (1078267 / 1000000) = -Real.log (1000000 / 1078267) := by
    rw [show ((1078267 / 1000000) : ℝ) = ((1000000 / 1078267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_816_neg : (16299937 / 200000000) ≤ -Real.log (921733 / 1000000) ∧
    -Real.log (921733 / 1000000) ≤ (40749843 / 500000000) := by
  have h := checkLog_sound (w := (78267 / 1921733)) (n := 12)
    (lo := (16299937 / 200000000)) (hi := (40749843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921733) = 1/(921733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_816 : Bounds (-40749843 / 500000000) (-16299937 / 200000000) (Real.log (921733 / 1000000)) := by
  have h := reflection_log_816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_817_neg : (37773539 / 500000000) ≤ -Real.log (500000 / 539237) ∧
    -Real.log (500000 / 539237) ≤ (75547079 / 1000000000) := by
  have h := checkLog_sound (w := (39237 / 1039237)) (n := 12)
    (lo := (37773539 / 500000000)) (hi := (75547079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539237 / 500000) = 1/(500000 / 539237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_817 : Bounds (37773539 / 500000000) (75547079 / 1000000000) (Real.log (539237 / 500000)) := by
  have h := reflection_log_817_neg
  have he : Real.log (539237 / 500000) = -Real.log (500000 / 539237) := by
    rw [show ((539237 / 500000) : ℝ) = ((500000 / 539237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_818_neg : (81724287 / 1000000000) ≤ -Real.log (460763 / 500000) ∧
    -Real.log (460763 / 500000) ≤ (638471 / 7812500) := by
  have h := checkLog_sound (w := (39237 / 960763)) (n := 12)
    (lo := (81724287 / 1000000000)) (hi := (638471 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460763) = 1/(460763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_818 : Bounds (-638471 / 7812500) (-81724287 / 1000000000) (Real.log (460763 / 500000)) := by
  have h := reflection_log_818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_819_neg : (772151 / 125000000) ≤ -Real.log (248460457831 / 250000000000) ∧
    -Real.log (248460457831 / 250000000000) ≤ (6177209 / 1000000000) := by
  have h := checkLog_sound (w := (1539542169 / 498460457831)) (n := 12)
    (lo := (772151 / 125000000)) (hi := (6177209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248460457831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248460457831) = 1/(248460457831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_819 : Bounds (-6177209 / 1000000000) (-772151 / 125000000) (Real.log (248460457831 / 250000000000)) := by
  have h := reflection_log_819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_820_neg : (3072281 / 500000000) ≤ -Real.log (993874276711 / 1000000000000) ∧
    -Real.log (993874276711 / 1000000000000) ≤ (6144563 / 1000000000) := by
  have h := checkLog_sound (w := (6125723289 / 1993874276711)) (n := 12)
    (lo := (3072281 / 500000000)) (hi := (6144563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993874276711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993874276711) = 1/(993874276711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_820 : Bounds (-6144563 / 1000000000) (-3072281 / 500000000) (Real.log (993874276711 / 1000000000000)) := by
  have h := reflection_log_820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_821_neg : (156854807 / 1000000000) ≤ -Real.log (500000000000 / 584912876071) ∧
    -Real.log (500000000000 / 584912876071) ≤ (19606851 / 125000000) := by
  have h := checkLog_sound (w := (84912876071 / 1084912876071)) (n := 12)
    (lo := (156854807 / 1000000000)) (hi := (19606851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584912876071 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584912876071 / 500000000000) = 1/(500000000000 / 584912876071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_821 : Bounds (156854807 / 1000000000) (19606851 / 125000000) (Real.log (584912876071 / 500000000000)) := by
  have h := reflection_log_821_neg
  have he : Real.log (584912876071 / 500000000000) = -Real.log (500000000000 / 584912876071) := by
    rw [show ((584912876071 / 500000000000) : ℝ) = ((500000000000 / 584912876071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_822_neg : (78635683 / 500000000) ≤ -Real.log (500000000000 / 585156577243) ∧
    -Real.log (500000000000 / 585156577243) ≤ (157271367 / 1000000000) := by
  have h := checkLog_sound (w := (85156577243 / 1085156577243)) (n := 12)
    (lo := (78635683 / 500000000)) (hi := (157271367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585156577243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585156577243 / 500000000000) = 1/(500000000000 / 585156577243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_822 : Bounds (78635683 / 500000000) (157271367 / 1000000000) (Real.log (585156577243 / 500000000000)) := by
  have h := reflection_log_822_neg
  have he : Real.log (585156577243 / 500000000000) = -Real.log (500000000000 / 585156577243) := by
    rw [show ((585156577243 / 500000000000) : ℝ) = ((500000000000 / 585156577243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_823_neg : (157284277 / 500000000) ≤ -Real.log (250000000000 / 342417061611) ∧
    -Real.log (250000000000 / 342417061611) ≤ (62913711 / 200000000) := by
  have h := checkLog_sound (w := (92417061611 / 592417061611)) (n := 12)
    (lo := (157284277 / 500000000)) (hi := (62913711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342417061611 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342417061611 / 250000000000) = 1/(250000000000 / 342417061611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_823 : Bounds (157284277 / 500000000) (62913711 / 200000000) (Real.log (342417061611 / 250000000000)) := by
  have h := reflection_log_823_neg
  have he : Real.log (342417061611 / 250000000000) = -Real.log (250000000000 / 342417061611) := by
    rw [show ((342417061611 / 250000000000) : ℝ) = ((250000000000 / 342417061611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_824_neg : (157386773 / 500000000) ≤ -Real.log (62500000000 / 85621815381) ∧
    -Real.log (62500000000 / 85621815381) ≤ (314773547 / 1000000000) := by
  have h := checkLog_sound (w := (23121815381 / 148121815381)) (n := 12)
    (lo := (157386773 / 500000000)) (hi := (314773547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85621815381 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85621815381 / 62500000000) = 1/(62500000000 / 85621815381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_824 : Bounds (157386773 / 500000000) (314773547 / 1000000000) (Real.log (85621815381 / 62500000000)) := by
  have h := reflection_log_824_neg
  have he : Real.log (85621815381 / 62500000000) = -Real.log (62500000000 / 85621815381) := by
    rw [show ((85621815381 / 62500000000) : ℝ) = ((62500000000 / 85621815381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_825_neg : (29027753 / 200000000) ≤ -Real.log (5000 / 5781) ∧
    -Real.log (5000 / 5781) ≤ (72569383 / 500000000) := by
  have h := checkLog_sound (w := (781 / 10781)) (n := 12)
    (lo := (29027753 / 200000000)) (hi := (72569383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5781 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5781 / 5000) = 1/(5000 / 5781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_825 : Bounds (29027753 / 200000000) (72569383 / 500000000) (Real.log (5781 / 5000)) := by
  have h := reflection_log_825_neg
  have he : Real.log (5781 / 5000) = -Real.log (5000 / 5781) := by
    rw [show ((5781 / 5000) : ℝ) = ((5000 / 5781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_826_neg : (169839779 / 1000000000) ≤ -Real.log (4219 / 5000) ∧
    -Real.log (4219 / 5000) ≤ (8491989 / 50000000) := by
  have h := checkLog_sound (w := (781 / 9219)) (n := 12)
    (lo := (169839779 / 1000000000)) (hi := (8491989 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4219) = 1/(4219 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_826 : Bounds (-8491989 / 50000000) (-169839779 / 1000000000) (Real.log (4219 / 5000)) := by
  have h := reflection_log_826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_827_neg : (156187 / 1000000000) ≤ -Real.log (5000000 / 5000781) ∧
    -Real.log (5000000 / 5000781) ≤ (39047 / 250000000) := by
  have h := checkLog_sound (w := (781 / 10000781)) (n := 12)
    (lo := (156187 / 1000000000)) (hi := (39047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000781 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000781 / 5000000) = 1/(5000000 / 5000781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_827 : Bounds (156187 / 1000000000) (39047 / 250000000) (Real.log (5000781 / 5000000)) := by
  have h := reflection_log_827_neg
  have he : Real.log (5000781 / 5000000) = -Real.log (5000000 / 5000781) := by
    rw [show ((5000781 / 5000000) : ℝ) = ((5000000 / 5000781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_828_neg : (39053 / 250000000) ≤ -Real.log (4999219 / 5000000) ∧
    -Real.log (4999219 / 5000000) ≤ (156213 / 1000000000) := by
  have h := checkLog_sound (w := (781 / 9999219)) (n := 12)
    (lo := (39053 / 250000000)) (hi := (156213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999219) = 1/(4999219 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_828 : Bounds (-156213 / 1000000000) (-39053 / 250000000) (Real.log (4999219 / 5000000)) := by
  have h := reflection_log_828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_829_neg : (18850373 / 250000000) ≤ -Real.log (1000000 / 1078317) ∧
    -Real.log (1000000 / 1078317) ≤ (75401493 / 1000000000) := by
  have h := checkLog_sound (w := (78317 / 2078317)) (n := 12)
    (lo := (18850373 / 250000000)) (hi := (75401493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078317 / 1000000) = 1/(1000000 / 1078317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_829 : Bounds (18850373 / 250000000) (75401493 / 1000000000) (Real.log (1078317 / 1000000)) := by
  have h := reflection_log_829_neg
  have he : Real.log (1078317 / 1000000) = -Real.log (1000000 / 1078317) := by
    rw [show ((1078317 / 1000000) : ℝ) = ((1000000 / 1078317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_830_neg : (20388483 / 250000000) ≤ -Real.log (921683 / 1000000) ∧
    -Real.log (921683 / 1000000) ≤ (81553933 / 1000000000) := by
  have h := checkLog_sound (w := (78317 / 1921683)) (n := 12)
    (lo := (20388483 / 250000000)) (hi := (81553933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921683) = 1/(921683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_830 : Bounds (-81553933 / 1000000000) (-20388483 / 250000000) (Real.log (921683 / 1000000)) := by
  have h := reflection_log_830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_831_neg : (75593439 / 1000000000) ≤ -Real.log (250000 / 269631) ∧
    -Real.log (250000 / 269631) ≤ (472459 / 6250000) := by
  have h := checkLog_sound (w := (19631 / 519631)) (n := 12)
    (lo := (75593439 / 1000000000)) (hi := (472459 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269631 / 250000) = 1/(250000 / 269631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_831 : Bounds (75593439 / 1000000000) (472459 / 6250000) (Real.log (269631 / 250000)) := by
  have h := reflection_log_831_neg
  have he : Real.log (269631 / 250000) = -Real.log (250000 / 269631) := by
    rw [show ((269631 / 250000) : ℝ) = ((250000 / 269631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


