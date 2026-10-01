-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0310Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0310Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:10:59.958594+00:00
-- url     : https://prove2.me/theorems/1a651e47-3f94-499b-9a24-24d3c851c7eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0310Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0311Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0310Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0311Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0312Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0313Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0314Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0315Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0316Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0317Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0310Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0311Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0312Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0313Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0314Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0315Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0316Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0317Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0310Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0311Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0312Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0313Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0314Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0315Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0316Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0317Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0310Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0311Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0312Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0313Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0314Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0315Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0316Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0317Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0310Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0310
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

theorem reflection_log_1_neg : (221579829 / 1000000000) ≤ -Real.log (512 / 639) ∧
    -Real.log (512 / 639) ≤ (22157983 / 100000000) := by
  have h := checkLog_sound (w := (127 / 1151)) (n := 12)
    (lo := (221579829 / 1000000000)) (hi := (22157983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639 / 512) = 1/(512 / 639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221579829 / 1000000000) (22157983 / 100000000) (Real.log (639 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (639 / 512) = -Real.log (512 / 639) := by
    rw [show ((639 / 512) : ℝ) = ((512 / 639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28508129 / 100000000) ≤ -Real.log (385 / 512) ∧
    -Real.log (385 / 512) ≤ (285081291 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 897)) (n := 12)
    (lo := (28508129 / 100000000)) (hi := (285081291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 385) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 385) = 1/(385 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-285081291 / 1000000000) (-28508129 / 100000000) (Real.log (385 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221345059 / 1000000000) ≤ -Real.log (10240 / 12777) ∧
    -Real.log (10240 / 12777) ≤ (11067253 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 23017)) (n := 12)
    (lo := (221345059 / 1000000000)) (hi := (11067253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12777 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12777 / 10240) = 1/(10240 / 12777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (221345059 / 1000000000) (11067253 / 50000000) (Real.log (12777 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12777 / 10240) = -Real.log (10240 / 12777) := by
    rw [show ((12777 / 10240) : ℝ) = ((10240 / 12777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71172939 / 250000000) ≤ -Real.log (7703 / 10240) ∧
    -Real.log (7703 / 10240) ≤ (284691757 / 1000000000) := by
  have h := checkLog_sound (w := (2537 / 17943)) (n := 12)
    (lo := (71172939 / 250000000)) (hi := (284691757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7703) = 1/(7703 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-284691757 / 1000000000) (-71172939 / 250000000) (Real.log (7703 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50357193 / 125000000) ≤ -Real.log (256 / 383) ∧
    -Real.log (256 / 383) ≤ (80571509 / 200000000) := by
  have h := checkLog_sound (w := (127 / 639)) (n := 12)
    (lo := (50357193 / 125000000)) (hi := (80571509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383 / 256) = 1/(256 / 383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50357193 / 125000000) (80571509 / 200000000) (Real.log (383 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (383 / 256) = -Real.log (256 / 383) := by
    rw [show ((383 / 256) : ℝ) = ((256 / 383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (8567063 / 12500000) ≤ -Real.log (129 / 256) ∧
    -Real.log (129 / 256) ≤ (685365041 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 385)) (n := 12)
    (lo := (8567063 / 12500000)) (hi := (685365041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 129) = 1/(129 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-685365041 / 1000000000) (-8567063 / 12500000) (Real.log (129 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (402465823 / 1000000000) ≤ -Real.log (5120 / 7657) ∧
    -Real.log (5120 / 7657) ≤ (12577057 / 31250000) := by
  have h := checkLog_sound (w := (2537 / 12777)) (n := 12)
    (lo := (402465823 / 1000000000)) (hi := (12577057 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7657 / 5120) = 1/(5120 / 7657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (402465823 / 1000000000) (12577057 / 31250000) (Real.log (7657 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7657 / 5120) = -Real.log (5120 / 7657) := by
    rw [show ((7657 / 5120) : ℝ) = ((5120 / 7657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171050731 / 250000000) ≤ -Real.log (2583 / 5120) ∧
    -Real.log (2583 / 5120) ≤ (27368117 / 40000000) := by
  have h := checkLog_sound (w := (2537 / 7703)) (n := 12)
    (lo := (171050731 / 250000000)) (hi := (27368117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2583) = 1/(2583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-27368117 / 40000000) (-171050731 / 250000000) (Real.log (2583 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303345261 / 1000000000) ≤ -Real.log (500000 / 677191) ∧
    -Real.log (500000 / 677191) ≤ (151672631 / 500000000) := by
  have h := checkLog_sound (w := (177191 / 1177191)) (n := 12)
    (lo := (303345261 / 1000000000)) (hi := (151672631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677191 / 500000) = 1/(500000 / 677191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303345261 / 1000000000) (151672631 / 500000000) (Real.log (677191 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (677191 / 500000) = -Real.log (500000 / 677191) := by
    rw [show ((677191 / 500000) : ℝ) = ((500000 / 677191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (437547281 / 1000000000) ≤ -Real.log (322809 / 500000) ∧
    -Real.log (322809 / 500000) ≤ (218773641 / 500000000) := by
  have h := checkLog_sound (w := (177191 / 822809)) (n := 12)
    (lo := (437547281 / 1000000000)) (hi := (218773641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322809) = 1/(322809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218773641 / 500000000) (-437547281 / 1000000000) (Real.log (322809 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (303663437 / 1000000000) ≤ -Real.log (1000000 / 1354813) ∧
    -Real.log (1000000 / 1354813) ≤ (151831719 / 500000000) := by
  have h := checkLog_sound (w := (354813 / 2354813)) (n := 12)
    (lo := (303663437 / 1000000000)) (hi := (151831719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354813 / 1000000) = 1/(1000000 / 1354813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (303663437 / 1000000000) (151831719 / 500000000) (Real.log (1354813 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1354813 / 1000000) = -Real.log (1000000 / 1354813) := by
    rw [show ((1354813 / 1000000) : ℝ) = ((1000000 / 1354813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (438215081 / 1000000000) ≤ -Real.log (645187 / 1000000) ∧
    -Real.log (645187 / 1000000) ≤ (219107541 / 500000000) := by
  have h := checkLog_sound (w := (354813 / 1645187)) (n := 12)
    (lo := (438215081 / 1000000000)) (hi := (219107541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645187) = 1/(645187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219107541 / 500000000) (-438215081 / 1000000000) (Real.log (645187 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230799767 / 1000000000) ≤ -Real.log (1000000 / 1259607) ∧
    -Real.log (1000000 / 1259607) ≤ (28849971 / 125000000) := by
  have h := checkLog_sound (w := (259607 / 2259607)) (n := 12)
    (lo := (230799767 / 1000000000)) (hi := (28849971 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259607 / 1000000) = 1/(1000000 / 1259607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230799767 / 1000000000) (28849971 / 125000000) (Real.log (1259607 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1259607 / 1000000) = -Real.log (1000000 / 1259607) := by
    rw [show ((1259607 / 1000000) : ℝ) = ((1000000 / 1259607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (37571769 / 125000000) ≤ -Real.log (740393 / 1000000) ∧
    -Real.log (740393 / 1000000) ≤ (300574153 / 1000000000) := by
  have h := checkLog_sound (w := (259607 / 1740393)) (n := 12)
    (lo := (37571769 / 125000000)) (hi := (300574153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740393) = 1/(740393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300574153 / 1000000000) (-37571769 / 125000000) (Real.log (740393 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231068069 / 1000000000) ≤ -Real.log (200000 / 251989) ∧
    -Real.log (200000 / 251989) ≤ (23106807 / 100000000) := by
  have h := checkLog_sound (w := (51989 / 451989)) (n := 12)
    (lo := (231068069 / 1000000000)) (hi := (23106807 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251989 / 200000) = 1/(200000 / 251989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231068069 / 1000000000) (23106807 / 100000000) (Real.log (251989 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (251989 / 200000) = -Real.log (200000 / 251989) := by
    rw [show ((251989 / 200000) : ℝ) = ((200000 / 251989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (301030771 / 1000000000) ≤ -Real.log (148011 / 200000) ∧
    -Real.log (148011 / 200000) ≤ (75257693 / 250000000) := by
  have h := checkLog_sound (w := (51989 / 348011)) (n := 12)
    (lo := (301030771 / 1000000000)) (hi := (75257693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148011) = 1/(148011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-75257693 / 250000000) (-301030771 / 1000000000) (Real.log (148011 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (370446271 / 500000000) ≤ -Real.log (50000000000 / 104890353119) ∧
    -Real.log (50000000000 / 104890353119) ≤ (5788223 / 7812500) := by
  have h := checkLog_sound (w := (4890353119 / 204890353119)) (n := 12)
    (lo := (23872681 / 500000000)) (hi := (47745363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104890353119 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104890353119 / 100000000000) = 1/(50000000000 / 104890353119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (370446271 / 500000000) (5788223 / 7812500) (Real.log (104890353119 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (104890353119 / 50000000000) = -Real.log (50000000000 / 104890353119) := by
    rw [show ((104890353119 / 50000000000) : ℝ) = ((50000000000 / 104890353119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (370939259 / 500000000) ≤ -Real.log (250000000000 / 524969117481) ∧
    -Real.log (250000000000 / 524969117481) ≤ (18546963 / 25000000) := by
  have h := checkLog_sound (w := (24969117481 / 1024969117481)) (n := 12)
    (lo := (24365669 / 500000000)) (hi := (48731339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((524969117481 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(524969117481 / 500000000000) = 1/(250000000000 / 524969117481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (370939259 / 500000000) (18546963 / 25000000) (Real.log (524969117481 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (524969117481 / 250000000000) = -Real.log (250000000000 / 524969117481) := by
    rw [show ((524969117481 / 250000000000) : ℝ) = ((250000000000 / 524969117481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3321087 / 6250000) ≤ -Real.log (500000000000 / 850634055157) ∧
    -Real.log (500000000000 / 850634055157) ≤ (531373921 / 1000000000) := by
  have h := checkLog_sound (w := (350634055157 / 1350634055157)) (n := 12)
    (lo := (3321087 / 6250000)) (hi := (531373921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850634055157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850634055157 / 500000000000) = 1/(500000000000 / 850634055157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3321087 / 6250000) (531373921 / 1000000000) (Real.log (850634055157 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (850634055157 / 500000000000) = -Real.log (500000000000 / 850634055157) := by
    rw [show ((850634055157 / 500000000000) : ℝ) = ((500000000000 / 850634055157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (13302471 / 25000000) ≤ -Real.log (25000000000 / 42562546027) ∧
    -Real.log (25000000000 / 42562546027) ≤ (532098841 / 1000000000) := by
  have h := checkLog_sound (w := (17562546027 / 67562546027)) (n := 12)
    (lo := (13302471 / 25000000)) (hi := (532098841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42562546027 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42562546027 / 25000000000) = 1/(25000000000 / 42562546027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (13302471 / 25000000) (532098841 / 1000000000) (Real.log (42562546027 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42562546027 / 25000000000) = -Real.log (25000000000 / 42562546027) := by
    rw [show ((42562546027 / 25000000000) : ℝ) = ((25000000000 / 42562546027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0310

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0311Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0311
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

theorem reflection_log_1_neg : (221345059 / 1000000000) ≤ -Real.log (10240 / 12777) ∧
    -Real.log (10240 / 12777) ≤ (11067253 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 23017)) (n := 12)
    (lo := (221345059 / 1000000000)) (hi := (11067253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12777 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12777 / 10240) = 1/(10240 / 12777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221345059 / 1000000000) (11067253 / 50000000) (Real.log (12777 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12777 / 10240) = -Real.log (10240 / 12777) := by
    rw [show ((12777 / 10240) : ℝ) = ((10240 / 12777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71172939 / 250000000) ≤ -Real.log (7703 / 10240) ∧
    -Real.log (7703 / 10240) ≤ (284691757 / 1000000000) := by
  have h := checkLog_sound (w := (2537 / 17943)) (n := 12)
    (lo := (71172939 / 250000000)) (hi := (284691757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7703) = 1/(7703 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-284691757 / 1000000000) (-71172939 / 250000000) (Real.log (7703 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44222047 / 200000000) ≤ -Real.log (5120 / 6387) ∧
    -Real.log (5120 / 6387) ≤ (55277559 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 11507)) (n := 12)
    (lo := (44222047 / 200000000)) (hi := (55277559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6387 / 5120) = 1/(5120 / 6387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44222047 / 200000000) (55277559 / 250000000) (Real.log (6387 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6387 / 5120) = -Real.log (5120 / 6387) := by
    rw [show ((6387 / 5120) : ℝ) = ((5120 / 6387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (284302373 / 1000000000) ≤ -Real.log (3853 / 5120) ∧
    -Real.log (3853 / 5120) ≤ (142151187 / 500000000) := by
  have h := checkLog_sound (w := (1267 / 8973)) (n := 12)
    (lo := (284302373 / 1000000000)) (hi := (142151187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3853) = 1/(3853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-142151187 / 500000000) (-284302373 / 1000000000) (Real.log (3853 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (402465823 / 1000000000) ≤ -Real.log (5120 / 7657) ∧
    -Real.log (5120 / 7657) ≤ (12577057 / 31250000) := by
  have h := checkLog_sound (w := (2537 / 12777)) (n := 12)
    (lo := (402465823 / 1000000000)) (hi := (12577057 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7657 / 5120) = 1/(5120 / 7657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (402465823 / 1000000000) (12577057 / 31250000) (Real.log (7657 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7657 / 5120) = -Real.log (5120 / 7657) := by
    rw [show ((7657 / 5120) : ℝ) = ((5120 / 7657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171050731 / 250000000) ≤ -Real.log (2583 / 5120) ∧
    -Real.log (2583 / 5120) ≤ (27368117 / 40000000) := by
  have h := checkLog_sound (w := (2537 / 7703)) (n := 12)
    (lo := (171050731 / 250000000)) (hi := (27368117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2583) = 1/(2583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-27368117 / 40000000) (-171050731 / 250000000) (Real.log (2583 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (402073947 / 1000000000) ≤ -Real.log (2560 / 3827) ∧
    -Real.log (2560 / 3827) ≤ (100518487 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 6387)) (n := 12)
    (lo := (402073947 / 1000000000)) (hi := (100518487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3827 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3827 / 2560) = 1/(2560 / 3827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (402073947 / 1000000000) (100518487 / 250000000) (Real.log (3827 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3827 / 2560) = -Real.log (2560 / 3827) := by
    rw [show ((3827 / 2560) : ℝ) = ((2560 / 3827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (341521079 / 500000000) ≤ -Real.log (1293 / 2560) ∧
    -Real.log (1293 / 2560) ≤ (683042159 / 1000000000) := by
  have h := checkLog_sound (w := (1267 / 3853)) (n := 12)
    (lo := (341521079 / 500000000)) (hi := (683042159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1293) = 1/(1293 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-683042159 / 1000000000) (-341521079 / 500000000) (Real.log (1293 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303028461 / 1000000000) ≤ -Real.log (1000000 / 1353953) ∧
    -Real.log (1000000 / 1353953) ≤ (151514231 / 500000000) := by
  have h := checkLog_sound (w := (353953 / 2353953)) (n := 12)
    (lo := (303028461 / 1000000000)) (hi := (151514231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353953 / 1000000) = 1/(1000000 / 1353953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303028461 / 1000000000) (151514231 / 500000000) (Real.log (1353953 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1353953 / 1000000) = -Real.log (1000000 / 1353953) := by
    rw [show ((1353953 / 1000000) : ℝ) = ((1000000 / 1353953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (218441511 / 500000000) ≤ -Real.log (646047 / 1000000) ∧
    -Real.log (646047 / 1000000) ≤ (436883023 / 1000000000) := by
  have h := checkLog_sound (w := (353953 / 1646047)) (n := 12)
    (lo := (218441511 / 500000000)) (hi := (436883023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646047) = 1/(646047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-436883023 / 1000000000) (-218441511 / 500000000) (Real.log (646047 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151673369 / 500000000) ≤ -Real.log (62500 / 84649) ∧
    -Real.log (62500 / 84649) ≤ (303346739 / 1000000000) := by
  have h := checkLog_sound (w := (22149 / 147149)) (n := 12)
    (lo := (151673369 / 500000000)) (hi := (303346739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84649 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84649 / 62500) = 1/(62500 / 84649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151673369 / 500000000) (303346739 / 1000000000) (Real.log (84649 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (84649 / 62500) = -Real.log (62500 / 84649) := by
    rw [show ((84649 / 62500) : ℝ) = ((62500 / 84649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (437550379 / 1000000000) ≤ -Real.log (40351 / 62500) ∧
    -Real.log (40351 / 62500) ≤ (21877519 / 50000000) := by
  have h := checkLog_sound (w := (22149 / 102851)) (n := 12)
    (lo := (437550379 / 1000000000)) (hi := (21877519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40351) = 1/(40351 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21877519 / 50000000) (-437550379 / 1000000000) (Real.log (40351 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230531393 / 1000000000) ≤ -Real.log (1000000 / 1259269) ∧
    -Real.log (1000000 / 1259269) ≤ (115265697 / 500000000) := by
  have h := checkLog_sound (w := (259269 / 2259269)) (n := 12)
    (lo := (230531393 / 1000000000)) (hi := (115265697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259269 / 1000000) = 1/(1000000 / 1259269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230531393 / 1000000000) (115265697 / 500000000) (Real.log (1259269 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1259269 / 1000000) = -Real.log (1000000 / 1259269) := by
    rw [show ((1259269 / 1000000) : ℝ) = ((1000000 / 1259269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150058871 / 500000000) ≤ -Real.log (740731 / 1000000) ∧
    -Real.log (740731 / 1000000) ≤ (300117743 / 1000000000) := by
  have h := checkLog_sound (w := (259269 / 1740731)) (n := 12)
    (lo := (150058871 / 500000000)) (hi := (300117743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740731) = 1/(740731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300117743 / 1000000000) (-150058871 / 500000000) (Real.log (740731 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (230800561 / 1000000000) ≤ -Real.log (125000 / 157451) ∧
    -Real.log (125000 / 157451) ≤ (115400281 / 500000000) := by
  have h := checkLog_sound (w := (32451 / 282451)) (n := 12)
    (lo := (230800561 / 1000000000)) (hi := (115400281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157451 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157451 / 125000) = 1/(125000 / 157451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (230800561 / 1000000000) (115400281 / 500000000) (Real.log (157451 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157451 / 125000) = -Real.log (125000 / 157451) := by
    rw [show ((157451 / 125000) : ℝ) = ((125000 / 157451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (300575503 / 1000000000) ≤ -Real.log (92549 / 125000) ∧
    -Real.log (92549 / 125000) ≤ (18785969 / 62500000) := by
  have h := checkLog_sound (w := (32451 / 217549)) (n := 12)
    (lo := (300575503 / 1000000000)) (hi := (18785969 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92549) = 1/(92549 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-18785969 / 62500000) (-300575503 / 1000000000) (Real.log (92549 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (739911483 / 1000000000) ≤ -Real.log (250000000000 / 523937499903) ∧
    -Real.log (250000000000 / 523937499903) ≤ (147982297 / 200000000) := by
  have h := checkLog_sound (w := (23937499903 / 1023937499903)) (n := 12)
    (lo := (46764303 / 1000000000)) (hi := (2922769 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523937499903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523937499903 / 500000000000) = 1/(250000000000 / 523937499903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (739911483 / 1000000000) (147982297 / 200000000) (Real.log (523937499903 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (523937499903 / 250000000000) = -Real.log (250000000000 / 523937499903) := by
    rw [show ((523937499903 / 250000000000) : ℝ) = ((250000000000 / 523937499903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (740897117 / 1000000000) ≤ -Real.log (50000000000 / 104890832941) ∧
    -Real.log (50000000000 / 104890832941) ≤ (740897119 / 1000000000) := by
  have h := checkLog_sound (w := (4890832941 / 204890832941)) (n := 12)
    (lo := (47749937 / 1000000000)) (hi := (23874969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104890832941 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104890832941 / 100000000000) = 1/(50000000000 / 104890832941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (740897117 / 1000000000) (740897119 / 1000000000) (Real.log (104890832941 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (104890832941 / 50000000000) = -Real.log (50000000000 / 104890832941) := by
    rw [show ((104890832941 / 50000000000) : ℝ) = ((50000000000 / 104890832941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33165571 / 62500000) ≤ -Real.log (500000000000 / 850017752733) ∧
    -Real.log (500000000000 / 850017752733) ≤ (530649137 / 1000000000) := by
  have h := checkLog_sound (w := (350017752733 / 1350017752733)) (n := 12)
    (lo := (33165571 / 62500000)) (hi := (530649137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850017752733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850017752733 / 500000000000) = 1/(500000000000 / 850017752733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33165571 / 62500000) (530649137 / 1000000000) (Real.log (850017752733 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (850017752733 / 500000000000) = -Real.log (500000000000 / 850017752733) := by
    rw [show ((850017752733 / 500000000000) : ℝ) = ((500000000000 / 850017752733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (8302751 / 15625000) ≤ -Real.log (500000000000 / 850635879373) ∧
    -Real.log (500000000000 / 850635879373) ≤ (106275213 / 200000000) := by
  have h := checkLog_sound (w := (350635879373 / 1350635879373)) (n := 12)
    (lo := (8302751 / 15625000)) (hi := (106275213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850635879373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850635879373 / 500000000000) = 1/(500000000000 / 850635879373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (8302751 / 15625000) (106275213 / 200000000) (Real.log (850635879373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (850635879373 / 500000000000) = -Real.log (500000000000 / 850635879373) := by
    rw [show ((850635879373 / 500000000000) : ℝ) = ((500000000000 / 850635879373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0311

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0312Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0312
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

theorem reflection_log_1_neg : (44222047 / 200000000) ≤ -Real.log (5120 / 6387) ∧
    -Real.log (5120 / 6387) ≤ (55277559 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 11507)) (n := 12)
    (lo := (44222047 / 200000000)) (hi := (55277559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6387 / 5120) = 1/(5120 / 6387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44222047 / 200000000) (55277559 / 250000000) (Real.log (6387 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6387 / 5120) = -Real.log (5120 / 6387) := by
    rw [show ((6387 / 5120) : ℝ) = ((5120 / 6387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (284302373 / 1000000000) ≤ -Real.log (3853 / 5120) ∧
    -Real.log (3853 / 5120) ≤ (142151187 / 500000000) := by
  have h := checkLog_sound (w := (1267 / 8973)) (n := 12)
    (lo := (284302373 / 1000000000)) (hi := (142151187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3853) = 1/(3853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-142151187 / 500000000) (-284302373 / 1000000000) (Real.log (3853 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44175071 / 200000000) ≤ -Real.log (10240 / 12771) ∧
    -Real.log (10240 / 12771) ≤ (55218839 / 250000000) := by
  have h := checkLog_sound (w := (2531 / 23011)) (n := 12)
    (lo := (44175071 / 200000000)) (hi := (55218839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12771 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12771 / 10240) = 1/(10240 / 12771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44175071 / 200000000) (55218839 / 250000000) (Real.log (12771 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12771 / 10240) = -Real.log (10240 / 12771) := by
    rw [show ((12771 / 10240) : ℝ) = ((10240 / 12771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141956571 / 500000000) ≤ -Real.log (7709 / 10240) ∧
    -Real.log (7709 / 10240) ≤ (283913143 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 17949)) (n := 12)
    (lo := (141956571 / 500000000)) (hi := (283913143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7709) = 1/(7709 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-283913143 / 1000000000) (-141956571 / 500000000) (Real.log (7709 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (402073947 / 1000000000) ≤ -Real.log (2560 / 3827) ∧
    -Real.log (2560 / 3827) ≤ (100518487 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 6387)) (n := 12)
    (lo := (402073947 / 1000000000)) (hi := (100518487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3827 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3827 / 2560) = 1/(2560 / 3827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (402073947 / 1000000000) (100518487 / 250000000) (Real.log (3827 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3827 / 2560) = -Real.log (2560 / 3827) := by
    rw [show ((3827 / 2560) : ℝ) = ((2560 / 3827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (341521079 / 500000000) ≤ -Real.log (1293 / 2560) ∧
    -Real.log (1293 / 2560) ≤ (683042159 / 1000000000) := by
  have h := checkLog_sound (w := (1267 / 3853)) (n := 12)
    (lo := (341521079 / 500000000)) (hi := (683042159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1293) = 1/(1293 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-683042159 / 1000000000) (-341521079 / 500000000) (Real.log (1293 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (401681919 / 1000000000) ≤ -Real.log (5120 / 7651) ∧
    -Real.log (5120 / 7651) ≤ (156907 / 390625) := by
  have h := checkLog_sound (w := (2531 / 12771)) (n := 12)
    (lo := (401681919 / 1000000000)) (hi := (156907 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7651 / 5120) = 1/(5120 / 7651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (401681919 / 1000000000) (156907 / 390625) (Real.log (7651 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7651 / 5120) = -Real.log (5120 / 7651) := by
    rw [show ((7651 / 5120) : ℝ) = ((5120 / 7651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (340941369 / 500000000) ≤ -Real.log (2589 / 5120) ∧
    -Real.log (2589 / 5120) ≤ (681882739 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 7709)) (n := 12)
    (lo := (340941369 / 500000000)) (hi := (681882739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2589) = 1/(2589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-681882739 / 1000000000) (-340941369 / 500000000) (Real.log (2589 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151355411 / 500000000) ≤ -Real.log (1000000 / 1353523) ∧
    -Real.log (1000000 / 1353523) ≤ (302710823 / 1000000000) := by
  have h := checkLog_sound (w := (353523 / 2353523)) (n := 12)
    (lo := (151355411 / 500000000)) (hi := (302710823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353523 / 1000000) = 1/(1000000 / 1353523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151355411 / 500000000) (302710823 / 1000000000) (Real.log (1353523 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1353523 / 1000000) = -Real.log (1000000 / 1353523) := by
    rw [show ((1353523 / 1000000) : ℝ) = ((1000000 / 1353523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (436217657 / 1000000000) ≤ -Real.log (646477 / 1000000) ∧
    -Real.log (646477 / 1000000) ≤ (218108829 / 500000000) := by
  have h := checkLog_sound (w := (353523 / 1646477)) (n := 12)
    (lo := (436217657 / 1000000000)) (hi := (218108829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646477) = 1/(646477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218108829 / 500000000) (-436217657 / 1000000000) (Real.log (646477 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (757573 / 2500000) ≤ -Real.log (500000 / 676977) ∧
    -Real.log (500000 / 676977) ≤ (303029201 / 1000000000) := by
  have h := checkLog_sound (w := (176977 / 1176977)) (n := 12)
    (lo := (757573 / 2500000)) (hi := (303029201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676977 / 500000) = 1/(500000 / 676977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (757573 / 2500000) (303029201 / 1000000000) (Real.log (676977 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (676977 / 500000) = -Real.log (500000 / 676977) := by
    rw [show ((676977 / 500000) : ℝ) = ((500000 / 676977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43688457 / 100000000) ≤ -Real.log (323023 / 500000) ∧
    -Real.log (323023 / 500000) ≤ (436884571 / 1000000000) := by
  have h := checkLog_sound (w := (176977 / 823023)) (n := 12)
    (lo := (43688457 / 100000000)) (hi := (436884571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 323023) = 1/(323023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-436884571 / 1000000000) (-43688457 / 100000000) (Real.log (323023 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (115131871 / 500000000) ≤ -Real.log (250000 / 314733) ∧
    -Real.log (250000 / 314733) ≤ (230263743 / 1000000000) := by
  have h := checkLog_sound (w := (64733 / 564733)) (n := 12)
    (lo := (115131871 / 500000000)) (hi := (230263743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314733 / 250000) = 1/(250000 / 314733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (115131871 / 500000000) (230263743 / 1000000000) (Real.log (314733 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (314733 / 250000) = -Real.log (250000 / 314733) := by
    rw [show ((314733 / 250000) : ℝ) = ((250000 / 314733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29966289 / 100000000) ≤ -Real.log (185267 / 250000) ∧
    -Real.log (185267 / 250000) ≤ (299662891 / 1000000000) := by
  have h := checkLog_sound (w := (64733 / 435267)) (n := 12)
    (lo := (29966289 / 100000000)) (hi := (299662891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185267) = 1/(185267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-299662891 / 1000000000) (-29966289 / 100000000) (Real.log (185267 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (230532187 / 1000000000) ≤ -Real.log (100000 / 125927) ∧
    -Real.log (100000 / 125927) ≤ (57633047 / 250000000) := by
  have h := checkLog_sound (w := (25927 / 225927)) (n := 12)
    (lo := (230532187 / 1000000000)) (hi := (57633047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125927 / 100000) = 1/(100000 / 125927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (230532187 / 1000000000) (57633047 / 250000000) (Real.log (125927 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125927 / 100000) = -Real.log (100000 / 125927) := by
    rw [show ((125927 / 100000) : ℝ) = ((100000 / 125927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (75029773 / 250000000) ≤ -Real.log (74073 / 100000) ∧
    -Real.log (74073 / 100000) ≤ (300119093 / 1000000000) := by
  have h := checkLog_sound (w := (25927 / 174073)) (n := 12)
    (lo := (75029773 / 250000000)) (hi := (300119093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74073) = 1/(74073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-300119093 / 1000000000) (-75029773 / 250000000) (Real.log (74073 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (738928479 / 1000000000) ≤ -Real.log (2000000000 / 4187381763) ∧
    -Real.log (2000000000 / 4187381763) ≤ (738928481 / 1000000000) := by
  have h := checkLog_sound (w := (187381763 / 8187381763)) (n := 12)
    (lo := (45781299 / 1000000000)) (hi := (457813 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187381763 / 4000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4187381763 / 4000000000) = 1/(2000000000 / 4187381763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (738928479 / 1000000000) (738928481 / 1000000000) (Real.log (4187381763 / 2000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4187381763 / 2000000000) = -Real.log (2000000000 / 4187381763) := by
    rw [show ((4187381763 / 2000000000) : ℝ) = ((2000000000 / 4187381763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73991377 / 100000000) ≤ -Real.log (31250000000 / 65492337233) ∧
    -Real.log (31250000000 / 65492337233) ≤ (184978443 / 250000000) := by
  have h := checkLog_sound (w := (2992337233 / 127992337233)) (n := 12)
    (lo := (4676659 / 100000000)) (hi := (46766591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65492337233 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65492337233 / 62500000000) = 1/(31250000000 / 65492337233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73991377 / 100000000) (184978443 / 250000000) (Real.log (65492337233 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65492337233 / 31250000000) = -Real.log (31250000000 / 65492337233) := by
    rw [show ((65492337233 / 31250000000) : ℝ) = ((31250000000 / 65492337233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (66240829 / 125000000) ≤ -Real.log (250000000000 / 424701916693) ∧
    -Real.log (250000000000 / 424701916693) ≤ (529926633 / 1000000000) := by
  have h := checkLog_sound (w := (174701916693 / 674701916693)) (n := 12)
    (lo := (66240829 / 125000000)) (hi := (529926633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424701916693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424701916693 / 250000000000) = 1/(250000000000 / 424701916693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (66240829 / 125000000) (529926633 / 1000000000) (Real.log (424701916693 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (424701916693 / 250000000000) = -Real.log (250000000000 / 424701916693) := by
    rw [show ((424701916693 / 250000000000) : ℝ) = ((250000000000 / 424701916693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (6633141 / 12500000) ≤ -Real.log (125000000000 / 212504893821) ∧
    -Real.log (125000000000 / 212504893821) ≤ (530651281 / 1000000000) := by
  have h := checkLog_sound (w := (87504893821 / 337504893821)) (n := 12)
    (lo := (6633141 / 12500000)) (hi := (530651281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212504893821 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212504893821 / 125000000000) = 1/(125000000000 / 212504893821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (6633141 / 12500000) (530651281 / 1000000000) (Real.log (212504893821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (212504893821 / 125000000000) = -Real.log (125000000000 / 212504893821) := by
    rw [show ((212504893821 / 125000000000) : ℝ) = ((125000000000 / 212504893821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0312

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0313Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0313
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

theorem reflection_log_1_neg : (44175071 / 200000000) ≤ -Real.log (10240 / 12771) ∧
    -Real.log (10240 / 12771) ≤ (55218839 / 250000000) := by
  have h := checkLog_sound (w := (2531 / 23011)) (n := 12)
    (lo := (44175071 / 200000000)) (hi := (55218839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12771 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12771 / 10240) = 1/(10240 / 12771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44175071 / 200000000) (55218839 / 250000000) (Real.log (12771 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12771 / 10240) = -Real.log (10240 / 12771) := by
    rw [show ((12771 / 10240) : ℝ) = ((10240 / 12771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141956571 / 500000000) ≤ -Real.log (7709 / 10240) ∧
    -Real.log (7709 / 10240) ≤ (283913143 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 17949)) (n := 12)
    (lo := (141956571 / 500000000)) (hi := (283913143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7709) = 1/(7709 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-283913143 / 1000000000) (-141956571 / 500000000) (Real.log (7709 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (220640421 / 1000000000) ≤ -Real.log (320 / 399) ∧
    -Real.log (320 / 399) ≤ (110320211 / 500000000) := by
  have h := checkLog_sound (w := (79 / 719)) (n := 12)
    (lo := (220640421 / 1000000000)) (hi := (110320211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 320) = 1/(320 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (220640421 / 1000000000) (110320211 / 500000000) (Real.log (399 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (399 / 320) = -Real.log (320 / 399) := by
    rw [show ((399 / 320) : ℝ) = ((320 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141762031 / 500000000) ≤ -Real.log (241 / 320) ∧
    -Real.log (241 / 320) ≤ (283524063 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 561)) (n := 12)
    (lo := (141762031 / 500000000)) (hi := (283524063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 241) = 1/(241 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-283524063 / 1000000000) (-141762031 / 500000000) (Real.log (241 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (401681919 / 1000000000) ≤ -Real.log (5120 / 7651) ∧
    -Real.log (5120 / 7651) ≤ (156907 / 390625) := by
  have h := checkLog_sound (w := (2531 / 12771)) (n := 12)
    (lo := (401681919 / 1000000000)) (hi := (156907 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7651 / 5120) = 1/(5120 / 7651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (401681919 / 1000000000) (156907 / 390625) (Real.log (7651 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7651 / 5120) = -Real.log (5120 / 7651) := by
    rw [show ((7651 / 5120) : ℝ) = ((5120 / 7651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (340941369 / 500000000) ≤ -Real.log (2589 / 5120) ∧
    -Real.log (2589 / 5120) ≤ (681882739 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 7709)) (n := 12)
    (lo := (340941369 / 500000000)) (hi := (681882739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2589) = 1/(2589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-681882739 / 1000000000) (-340941369 / 500000000) (Real.log (2589 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50161217 / 125000000) ≤ -Real.log (160 / 239) ∧
    -Real.log (160 / 239) ≤ (401289737 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399)) (n := 12)
    (lo := (50161217 / 125000000)) (hi := (401289737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 160) = 1/(160 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50161217 / 125000000) (401289737 / 1000000000) (Real.log (239 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (239 / 160) = -Real.log (160 / 239) := by
    rw [show ((239 / 160) : ℝ) = ((160 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (34036233 / 50000000) ≤ -Real.log (81 / 160) ∧
    -Real.log (81 / 160) ≤ (680724661 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 81) = 1/(81 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-680724661 / 1000000000) (-34036233 / 50000000) (Real.log (81 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151196911 / 500000000) ≤ -Real.log (500000 / 676547) ∧
    -Real.log (500000 / 676547) ≤ (302393823 / 1000000000) := by
  have h := checkLog_sound (w := (176547 / 1176547)) (n := 12)
    (lo := (151196911 / 500000000)) (hi := (302393823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676547 / 500000) = 1/(500000 / 676547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151196911 / 500000000) (302393823 / 1000000000) (Real.log (676547 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (676547 / 500000) = -Real.log (500000 / 676547) := by
    rw [show ((676547 / 500000) : ℝ) = ((500000 / 676547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10888857 / 25000000) ≤ -Real.log (323453 / 500000) ∧
    -Real.log (323453 / 500000) ≤ (435554281 / 1000000000) := by
  have h := checkLog_sound (w := (176547 / 823453)) (n := 12)
    (lo := (10888857 / 25000000)) (hi := (435554281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 323453) = 1/(323453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-435554281 / 1000000000) (-10888857 / 25000000) (Real.log (323453 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302711561 / 1000000000) ≤ -Real.log (250000 / 338381) ∧
    -Real.log (250000 / 338381) ≤ (151355781 / 500000000) := by
  have h := checkLog_sound (w := (88381 / 588381)) (n := 12)
    (lo := (302711561 / 1000000000)) (hi := (151355781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338381 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338381 / 250000) = 1/(250000 / 338381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302711561 / 1000000000) (151355781 / 500000000) (Real.log (338381 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (338381 / 250000) = -Real.log (250000 / 338381) := by
    rw [show ((338381 / 250000) : ℝ) = ((250000 / 338381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109054801 / 250000000) ≤ -Real.log (161619 / 250000) ∧
    -Real.log (161619 / 250000) ≤ (87243841 / 200000000) := by
  have h := checkLog_sound (w := (88381 / 411619)) (n := 12)
    (lo := (109054801 / 250000000)) (hi := (87243841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161619) = 1/(161619 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87243841 / 200000000) (-109054801 / 250000000) (Real.log (161619 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (229996019 / 1000000000) ≤ -Real.log (200000 / 251719) ∧
    -Real.log (200000 / 251719) ≤ (11499801 / 50000000) := by
  have h := checkLog_sound (w := (51719 / 451719)) (n := 12)
    (lo := (229996019 / 1000000000)) (hi := (11499801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251719 / 200000) = 1/(200000 / 251719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (229996019 / 1000000000) (11499801 / 50000000) (Real.log (251719 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (251719 / 200000) = -Real.log (200000 / 251719) := by
    rw [show ((251719 / 200000) : ℝ) = ((200000 / 251719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74802061 / 250000000) ≤ -Real.log (148281 / 200000) ∧
    -Real.log (148281 / 200000) ≤ (59841649 / 200000000) := by
  have h := checkLog_sound (w := (51719 / 348281)) (n := 12)
    (lo := (74802061 / 250000000)) (hi := (59841649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148281) = 1/(148281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59841649 / 200000000) (-74802061 / 250000000) (Real.log (148281 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28783067 / 125000000) ≤ -Real.log (1000000 / 1258933) ∧
    -Real.log (1000000 / 1258933) ≤ (230264537 / 1000000000) := by
  have h := checkLog_sound (w := (258933 / 2258933)) (n := 12)
    (lo := (28783067 / 125000000)) (hi := (230264537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258933 / 1000000) = 1/(1000000 / 1258933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28783067 / 125000000) (230264537 / 1000000000) (Real.log (1258933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1258933 / 1000000) = -Real.log (1000000 / 1258933) := by
    rw [show ((1258933 / 1000000) : ℝ) = ((1000000 / 1258933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299664239 / 1000000000) ≤ -Real.log (741067 / 1000000) ∧
    -Real.log (741067 / 1000000) ≤ (3745803 / 12500000) := by
  have h := checkLog_sound (w := (258933 / 1741067)) (n := 12)
    (lo := (299664239 / 1000000000)) (hi := (3745803 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741067) = 1/(741067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3745803 / 12500000) (-299664239 / 1000000000) (Real.log (741067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (368974051 / 500000000) ≤ -Real.log (500000000000 / 1045819639947) ∧
    -Real.log (500000000000 / 1045819639947) ≤ (92243513 / 125000000) := by
  have h := checkLog_sound (w := (45819639947 / 2045819639947)) (n := 12)
    (lo := (22400461 / 500000000)) (hi := (44800923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1045819639947 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1045819639947 / 1000000000000) = 1/(500000000000 / 1045819639947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (368974051 / 500000000) (92243513 / 125000000) (Real.log (1045819639947 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1045819639947 / 500000000000) = -Real.log (500000000000 / 1045819639947) := by
    rw [show ((1045819639947 / 500000000000) : ℝ) = ((500000000000 / 1045819639947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (147786153 / 200000000) ≤ -Real.log (100000000000 / 209369566697) ∧
    -Real.log (100000000000 / 209369566697) ≤ (738930767 / 1000000000) := by
  have h := checkLog_sound (w := (9369566697 / 409369566697)) (n := 12)
    (lo := (9156717 / 200000000)) (hi := (22891793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209369566697 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209369566697 / 200000000000) = 1/(100000000000 / 209369566697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (147786153 / 200000000) (738930767 / 1000000000) (Real.log (209369566697 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (209369566697 / 100000000000) = -Real.log (100000000000 / 209369566697) := by
    rw [show ((209369566697 / 100000000000) : ℝ) = ((100000000000 / 209369566697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (529204263 / 1000000000) ≤ -Real.log (31250000000 / 53049404509) ∧
    -Real.log (31250000000 / 53049404509) ≤ (66150533 / 125000000) := by
  have h := checkLog_sound (w := (21799404509 / 84299404509)) (n := 12)
    (lo := (529204263 / 1000000000)) (hi := (66150533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53049404509 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53049404509 / 31250000000) = 1/(31250000000 / 53049404509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (529204263 / 1000000000) (66150533 / 125000000) (Real.log (53049404509 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53049404509 / 31250000000) = -Real.log (31250000000 / 53049404509) := by
    rw [show ((53049404509 / 31250000000) : ℝ) = ((31250000000 / 53049404509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (66241097 / 125000000) ≤ -Real.log (12500000000 / 21235141357) ∧
    -Real.log (12500000000 / 21235141357) ≤ (529928777 / 1000000000) := by
  have h := checkLog_sound (w := (8735141357 / 33735141357)) (n := 12)
    (lo := (66241097 / 125000000)) (hi := (529928777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21235141357 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21235141357 / 12500000000) = 1/(12500000000 / 21235141357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (66241097 / 125000000) (529928777 / 1000000000) (Real.log (21235141357 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21235141357 / 12500000000) = -Real.log (12500000000 / 21235141357) := by
    rw [show ((21235141357 / 12500000000) : ℝ) = ((12500000000 / 21235141357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0313

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0314Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0314
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

theorem reflection_log_1_neg : (220640421 / 1000000000) ≤ -Real.log (320 / 399) ∧
    -Real.log (320 / 399) ≤ (110320211 / 500000000) := by
  have h := checkLog_sound (w := (79 / 719)) (n := 12)
    (lo := (220640421 / 1000000000)) (hi := (110320211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 320) = 1/(320 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (220640421 / 1000000000) (110320211 / 500000000) (Real.log (399 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (399 / 320) = -Real.log (320 / 399) := by
    rw [show ((399 / 320) : ℝ) = ((320 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141762031 / 500000000) ≤ -Real.log (241 / 320) ∧
    -Real.log (241 / 320) ≤ (283524063 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 561)) (n := 12)
    (lo := (141762031 / 500000000)) (hi := (283524063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 241) = 1/(241 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-283524063 / 1000000000) (-141762031 / 500000000) (Real.log (241 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (220405431 / 1000000000) ≤ -Real.log (2048 / 2553) ∧
    -Real.log (2048 / 2553) ≤ (27550679 / 125000000) := by
  have h := checkLog_sound (w := (505 / 4601)) (n := 12)
    (lo := (220405431 / 1000000000)) (hi := (27550679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2553 / 2048) = 1/(2048 / 2553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (220405431 / 1000000000) (27550679 / 125000000) (Real.log (2553 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2553 / 2048) = -Real.log (2048 / 2553) := by
    rw [show ((2553 / 2048) : ℝ) = ((2048 / 2553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (283135133 / 1000000000) ≤ -Real.log (1543 / 2048) ∧
    -Real.log (1543 / 2048) ≤ (141567567 / 500000000) := by
  have h := checkLog_sound (w := (505 / 3591)) (n := 12)
    (lo := (283135133 / 1000000000)) (hi := (141567567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1543) = 1/(1543 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-141567567 / 500000000) (-283135133 / 1000000000) (Real.log (1543 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50161217 / 125000000) ≤ -Real.log (160 / 239) ∧
    -Real.log (160 / 239) ≤ (401289737 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399)) (n := 12)
    (lo := (50161217 / 125000000)) (hi := (401289737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 160) = 1/(160 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50161217 / 125000000) (401289737 / 1000000000) (Real.log (239 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (239 / 160) = -Real.log (160 / 239) := by
    rw [show ((239 / 160) : ℝ) = ((160 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (34036233 / 50000000) ≤ -Real.log (81 / 160) ∧
    -Real.log (81 / 160) ≤ (680724661 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 81) = 1/(81 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-680724661 / 1000000000) (-34036233 / 50000000) (Real.log (81 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2004487 / 5000000) ≤ -Real.log (1024 / 1529) ∧
    -Real.log (1024 / 1529) ≤ (400897401 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 2553)) (n := 12)
    (lo := (2004487 / 5000000)) (hi := (400897401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1529 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1529 / 1024) = 1/(1024 / 1529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2004487 / 5000000) (400897401 / 1000000000) (Real.log (1529 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1529 / 1024) = -Real.log (1024 / 1529) := by
    rw [show ((1529 / 1024) : ℝ) = ((1024 / 1529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (339783961 / 500000000) ≤ -Real.log (519 / 1024) ∧
    -Real.log (519 / 1024) ≤ (679567923 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 1543)) (n := 12)
    (lo := (339783961 / 500000000)) (hi := (679567923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 519) = 1/(519 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-679567923 / 1000000000) (-339783961 / 500000000) (Real.log (519 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (302075981 / 1000000000) ≤ -Real.log (125000 / 169083) ∧
    -Real.log (125000 / 169083) ≤ (151037991 / 500000000) := by
  have h := checkLog_sound (w := (44083 / 294083)) (n := 12)
    (lo := (302075981 / 1000000000)) (hi := (151037991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169083 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169083 / 125000) = 1/(125000 / 169083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (302075981 / 1000000000) (151037991 / 500000000) (Real.log (169083 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169083 / 125000) = -Real.log (125000 / 169083) := by
    rw [show ((169083 / 125000) : ℝ) = ((125000 / 169083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (434889799 / 1000000000) ≤ -Real.log (80917 / 125000) ∧
    -Real.log (80917 / 125000) ≤ (2174449 / 5000000) := by
  have h := checkLog_sound (w := (44083 / 205917)) (n := 12)
    (lo := (434889799 / 1000000000)) (hi := (2174449 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80917) = 1/(80917 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2174449 / 5000000) (-434889799 / 1000000000) (Real.log (80917 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302394561 / 1000000000) ≤ -Real.log (200000 / 270619) ∧
    -Real.log (200000 / 270619) ≤ (151197281 / 500000000) := by
  have h := checkLog_sound (w := (70619 / 470619)) (n := 12)
    (lo := (302394561 / 1000000000)) (hi := (151197281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270619 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270619 / 200000) = 1/(200000 / 270619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302394561 / 1000000000) (151197281 / 500000000) (Real.log (270619 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (270619 / 200000) = -Real.log (200000 / 270619) := by
    rw [show ((270619 / 200000) : ℝ) = ((200000 / 270619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (217777913 / 500000000) ≤ -Real.log (129381 / 200000) ∧
    -Real.log (129381 / 200000) ≤ (435555827 / 1000000000) := by
  have h := checkLog_sound (w := (70619 / 329381)) (n := 12)
    (lo := (217777913 / 500000000)) (hi := (435555827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129381) = 1/(129381 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-435555827 / 1000000000) (-217777913 / 500000000) (Real.log (129381 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7179007 / 31250000) ≤ -Real.log (500000 / 629129) ∧
    -Real.log (500000 / 629129) ≤ (9189129 / 40000000) := by
  have h := checkLog_sound (w := (129129 / 1129129)) (n := 12)
    (lo := (7179007 / 31250000)) (hi := (9189129 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629129 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629129 / 500000) = 1/(500000 / 629129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7179007 / 31250000) (9189129 / 40000000) (Real.log (629129 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (629129 / 500000) = -Real.log (500000 / 629129) := by
    rw [show ((629129 / 500000) : ℝ) = ((500000 / 629129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (59750761 / 200000000) ≤ -Real.log (370871 / 500000) ∧
    -Real.log (370871 / 500000) ≤ (149376903 / 500000000) := by
  have h := checkLog_sound (w := (129129 / 870871)) (n := 12)
    (lo := (59750761 / 200000000)) (hi := (149376903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370871) = 1/(370871 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-149376903 / 500000000) (-59750761 / 200000000) (Real.log (370871 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229996813 / 1000000000) ≤ -Real.log (250000 / 314649) ∧
    -Real.log (250000 / 314649) ≤ (114998407 / 500000000) := by
  have h := checkLog_sound (w := (64649 / 564649)) (n := 12)
    (lo := (229996813 / 1000000000)) (hi := (114998407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314649 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314649 / 250000) = 1/(250000 / 314649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229996813 / 1000000000) (114998407 / 500000000) (Real.log (314649 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (314649 / 250000) = -Real.log (250000 / 314649) := by
    rw [show ((314649 / 250000) : ℝ) = ((250000 / 314649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299209593 / 1000000000) ≤ -Real.log (185351 / 250000) ∧
    -Real.log (185351 / 250000) ≤ (149604797 / 500000000) := by
  have h := checkLog_sound (w := (64649 / 435351)) (n := 12)
    (lo := (299209593 / 1000000000)) (hi := (149604797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185351) = 1/(185351 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-149604797 / 500000000) (-299209593 / 1000000000) (Real.log (185351 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36848289 / 50000000) ≤ -Real.log (125000000000 / 261198203097) ∧
    -Real.log (125000000000 / 261198203097) ≤ (368482891 / 500000000) := by
  have h := checkLog_sound (w := (11198203097 / 511198203097)) (n := 12)
    (lo := (219093 / 5000000)) (hi := (43818601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261198203097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261198203097 / 250000000000) = 1/(125000000000 / 261198203097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36848289 / 50000000) (368482891 / 500000000) (Real.log (261198203097 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (261198203097 / 125000000000) = -Real.log (125000000000 / 261198203097) := by
    rw [show ((261198203097 / 125000000000) : ℝ) = ((125000000000 / 261198203097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (737950387 / 1000000000) ≤ -Real.log (50000000000 / 104582202951) ∧
    -Real.log (50000000000 / 104582202951) ≤ (737950389 / 1000000000) := by
  have h := checkLog_sound (w := (4582202951 / 204582202951)) (n := 12)
    (lo := (44803207 / 1000000000)) (hi := (5600401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104582202951 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104582202951 / 100000000000) = 1/(50000000000 / 104582202951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (737950387 / 1000000000) (737950389 / 1000000000) (Real.log (104582202951 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (104582202951 / 50000000000) = -Real.log (50000000000 / 104582202951) := by
    rw [show ((104582202951 / 50000000000) : ℝ) = ((50000000000 / 104582202951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (528482029 / 1000000000) ≤ -Real.log (100000000000 / 169635533649) ∧
    -Real.log (100000000000 / 169635533649) ≤ (52848203 / 100000000) := by
  have h := checkLog_sound (w := (69635533649 / 269635533649)) (n := 12)
    (lo := (528482029 / 1000000000)) (hi := (52848203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169635533649 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169635533649 / 100000000000) = 1/(100000000000 / 169635533649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (528482029 / 1000000000) (52848203 / 100000000) (Real.log (169635533649 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (169635533649 / 100000000000) = -Real.log (100000000000 / 169635533649) := by
    rw [show ((169635533649 / 100000000000) : ℝ) = ((100000000000 / 169635533649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (529206407 / 1000000000) ≤ -Real.log (500000000000 / 848792291383) ∧
    -Real.log (500000000000 / 848792291383) ≤ (66150801 / 125000000) := by
  have h := checkLog_sound (w := (348792291383 / 1348792291383)) (n := 12)
    (lo := (529206407 / 1000000000)) (hi := (66150801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848792291383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848792291383 / 500000000000) = 1/(500000000000 / 848792291383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (529206407 / 1000000000) (66150801 / 125000000) (Real.log (848792291383 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (848792291383 / 500000000000) = -Real.log (500000000000 / 848792291383) := by
    rw [show ((848792291383 / 500000000000) : ℝ) = ((500000000000 / 848792291383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0314

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0315Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0315
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

theorem reflection_log_1_neg : (220405431 / 1000000000) ≤ -Real.log (2048 / 2553) ∧
    -Real.log (2048 / 2553) ≤ (27550679 / 125000000) := by
  have h := checkLog_sound (w := (505 / 4601)) (n := 12)
    (lo := (220405431 / 1000000000)) (hi := (27550679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2553 / 2048) = 1/(2048 / 2553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (220405431 / 1000000000) (27550679 / 125000000) (Real.log (2553 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2553 / 2048) = -Real.log (2048 / 2553) := by
    rw [show ((2553 / 2048) : ℝ) = ((2048 / 2553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (283135133 / 1000000000) ≤ -Real.log (1543 / 2048) ∧
    -Real.log (1543 / 2048) ≤ (141567567 / 500000000) := by
  have h := checkLog_sound (w := (505 / 3591)) (n := 12)
    (lo := (283135133 / 1000000000)) (hi := (141567567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1543) = 1/(1543 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-141567567 / 500000000) (-283135133 / 1000000000) (Real.log (1543 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44034077 / 200000000) ≤ -Real.log (5120 / 6381) ∧
    -Real.log (5120 / 6381) ≤ (110085193 / 500000000) := by
  have h := checkLog_sound (w := (1261 / 11501)) (n := 12)
    (lo := (44034077 / 200000000)) (hi := (110085193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6381 / 5120) = 1/(5120 / 6381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44034077 / 200000000) (110085193 / 500000000) (Real.log (6381 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6381 / 5120) = -Real.log (5120 / 6381) := by
    rw [show ((6381 / 5120) : ℝ) = ((5120 / 6381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (70686589 / 250000000) ≤ -Real.log (3859 / 5120) ∧
    -Real.log (3859 / 5120) ≤ (282746357 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 8979)) (n := 12)
    (lo := (70686589 / 250000000)) (hi := (282746357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3859) = 1/(3859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-282746357 / 1000000000) (-70686589 / 250000000) (Real.log (3859 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2004487 / 5000000) ≤ -Real.log (1024 / 1529) ∧
    -Real.log (1024 / 1529) ≤ (400897401 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 2553)) (n := 12)
    (lo := (2004487 / 5000000)) (hi := (400897401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1529 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1529 / 1024) = 1/(1024 / 1529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2004487 / 5000000) (400897401 / 1000000000) (Real.log (1529 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1529 / 1024) = -Real.log (1024 / 1529) := by
    rw [show ((1529 / 1024) : ℝ) = ((1024 / 1529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (339783961 / 500000000) ≤ -Real.log (519 / 1024) ∧
    -Real.log (519 / 1024) ≤ (679567923 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 1543)) (n := 12)
    (lo := (339783961 / 500000000)) (hi := (679567923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 519) = 1/(519 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-679567923 / 1000000000) (-339783961 / 500000000) (Real.log (519 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (400504909 / 1000000000) ≤ -Real.log (2560 / 3821) ∧
    -Real.log (2560 / 3821) ≤ (40050491 / 100000000) := by
  have h := checkLog_sound (w := (1261 / 6381)) (n := 12)
    (lo := (400504909 / 1000000000)) (hi := (40050491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3821 / 2560) = 1/(2560 / 3821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (400504909 / 1000000000) (40050491 / 100000000) (Real.log (3821 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3821 / 2560) = -Real.log (2560 / 3821) := by
    rw [show ((3821 / 2560) : ℝ) = ((2560 / 3821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16960313 / 25000000) ≤ -Real.log (1299 / 2560) ∧
    -Real.log (1299 / 2560) ≤ (678412521 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 3859)) (n := 12)
    (lo := (16960313 / 25000000)) (hi := (678412521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1299) = 1/(1299 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-678412521 / 1000000000) (-16960313 / 25000000) (Real.log (1299 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (301758779 / 1000000000) ≤ -Real.log (200000 / 270447) ∧
    -Real.log (200000 / 270447) ≤ (15087939 / 50000000) := by
  have h := checkLog_sound (w := (70447 / 470447)) (n := 12)
    (lo := (301758779 / 1000000000)) (hi := (15087939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270447 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270447 / 200000) = 1/(200000 / 270447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (301758779 / 1000000000) (15087939 / 50000000) (Real.log (270447 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (270447 / 200000) = -Real.log (200000 / 270447) := by
    rw [show ((270447 / 200000) : ℝ) = ((200000 / 270447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (217113651 / 500000000) ≤ -Real.log (129553 / 200000) ∧
    -Real.log (129553 / 200000) ≤ (434227303 / 1000000000) := by
  have h := checkLog_sound (w := (70447 / 329553)) (n := 12)
    (lo := (217113651 / 500000000)) (hi := (434227303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129553) = 1/(129553 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-434227303 / 1000000000) (-217113651 / 500000000) (Real.log (129553 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3775959 / 12500000) ≤ -Real.log (200000 / 270533) ∧
    -Real.log (200000 / 270533) ≤ (302076721 / 1000000000) := by
  have h := checkLog_sound (w := (70533 / 470533)) (n := 12)
    (lo := (3775959 / 12500000)) (hi := (302076721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270533 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270533 / 200000) = 1/(200000 / 270533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3775959 / 12500000) (302076721 / 1000000000) (Real.log (270533 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (270533 / 200000) = -Real.log (200000 / 270533) := by
    rw [show ((270533 / 200000) : ℝ) = ((200000 / 270533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27180709 / 62500000) ≤ -Real.log (129467 / 200000) ∧
    -Real.log (129467 / 200000) ≤ (86978269 / 200000000) := by
  have h := checkLog_sound (w := (70533 / 329467)) (n := 12)
    (lo := (27180709 / 62500000)) (hi := (86978269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129467) = 1/(129467 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86978269 / 200000000) (-27180709 / 62500000) (Real.log (129467 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (114730179 / 500000000) ≤ -Real.log (1000000 / 1257921) ∧
    -Real.log (1000000 / 1257921) ≤ (229460359 / 1000000000) := by
  have h := checkLog_sound (w := (257921 / 2257921)) (n := 12)
    (lo := (114730179 / 500000000)) (hi := (229460359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257921 / 1000000) = 1/(1000000 / 1257921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (114730179 / 500000000) (229460359 / 1000000000) (Real.log (1257921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1257921 / 1000000) = -Real.log (1000000 / 1257921) := by
    rw [show ((1257921 / 1000000) : ℝ) = ((1000000 / 1257921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74574893 / 250000000) ≤ -Real.log (742079 / 1000000) ∧
    -Real.log (742079 / 1000000) ≤ (298299573 / 1000000000) := by
  have h := checkLog_sound (w := (257921 / 1742079)) (n := 12)
    (lo := (74574893 / 250000000)) (hi := (298299573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742079) = 1/(742079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-298299573 / 1000000000) (-74574893 / 250000000) (Real.log (742079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229729019 / 1000000000) ≤ -Real.log (1000000 / 1258259) ∧
    -Real.log (1000000 / 1258259) ≤ (11486451 / 50000000) := by
  have h := checkLog_sound (w := (258259 / 2258259)) (n := 12)
    (lo := (229729019 / 1000000000)) (hi := (11486451 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258259 / 1000000) = 1/(1000000 / 1258259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229729019 / 1000000000) (11486451 / 50000000) (Real.log (1258259 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1258259 / 1000000) = -Real.log (1000000 / 1258259) := by
    rw [show ((1258259 / 1000000) : ℝ) = ((1000000 / 1258259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (298755153 / 1000000000) ≤ -Real.log (741741 / 1000000) ∧
    -Real.log (741741 / 1000000) ≤ (149377577 / 500000000) := by
  have h := checkLog_sound (w := (258259 / 1741741)) (n := 12)
    (lo := (298755153 / 1000000000)) (hi := (149377577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741741) = 1/(741741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-149377577 / 500000000) (-298755153 / 1000000000) (Real.log (741741 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (735986081 / 1000000000) ≤ -Real.log (250000000000 / 521884865653) ∧
    -Real.log (250000000000 / 521884865653) ≤ (735986083 / 1000000000) := by
  have h := checkLog_sound (w := (21884865653 / 1021884865653)) (n := 12)
    (lo := (42838901 / 1000000000)) (hi := (21419451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((521884865653 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(521884865653 / 500000000000) = 1/(250000000000 / 521884865653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (735986081 / 1000000000) (735986083 / 1000000000) (Real.log (521884865653 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (521884865653 / 250000000000) = -Real.log (250000000000 / 521884865653) := by
    rw [show ((521884865653 / 250000000000) : ℝ) = ((250000000000 / 521884865653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5757563 / 7812500) ≤ -Real.log (500000000000 / 1044795198777) ∧
    -Real.log (500000000000 / 1044795198777) ≤ (368484033 / 500000000) := by
  have h := checkLog_sound (w := (44795198777 / 2044795198777)) (n := 12)
    (lo := (10955221 / 250000000)) (hi := (8764177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1044795198777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1044795198777 / 1000000000000) = 1/(500000000000 / 1044795198777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5757563 / 7812500) (368484033 / 500000000) (Real.log (1044795198777 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1044795198777 / 500000000000) = -Real.log (500000000000 / 1044795198777) := by
    rw [show ((1044795198777 / 500000000000) : ℝ) = ((500000000000 / 1044795198777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52775993 / 100000000) ≤ -Real.log (125000000000 / 211891355233) ∧
    -Real.log (125000000000 / 211891355233) ≤ (527759931 / 1000000000) := by
  have h := checkLog_sound (w := (86891355233 / 336891355233)) (n := 12)
    (lo := (52775993 / 100000000)) (hi := (527759931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211891355233 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211891355233 / 125000000000) = 1/(125000000000 / 211891355233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52775993 / 100000000) (527759931 / 1000000000) (Real.log (211891355233 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (211891355233 / 125000000000) = -Real.log (125000000000 / 211891355233) := by
    rw [show ((211891355233 / 125000000000) : ℝ) = ((125000000000 / 211891355233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (132121043 / 250000000) ≤ -Real.log (62500000000 / 106022435729) ∧
    -Real.log (62500000000 / 106022435729) ≤ (528484173 / 1000000000) := by
  have h := checkLog_sound (w := (43522435729 / 168522435729)) (n := 12)
    (lo := (132121043 / 250000000)) (hi := (528484173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106022435729 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106022435729 / 62500000000) = 1/(62500000000 / 106022435729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (132121043 / 250000000) (528484173 / 1000000000) (Real.log (106022435729 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (106022435729 / 62500000000) = -Real.log (62500000000 / 106022435729) := by
    rw [show ((106022435729 / 62500000000) : ℝ) = ((62500000000 / 106022435729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0315

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0316Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0316
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

theorem reflection_log_1_neg : (44034077 / 200000000) ≤ -Real.log (5120 / 6381) ∧
    -Real.log (5120 / 6381) ≤ (110085193 / 500000000) := by
  have h := checkLog_sound (w := (1261 / 11501)) (n := 12)
    (lo := (44034077 / 200000000)) (hi := (110085193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6381 / 5120) = 1/(5120 / 6381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44034077 / 200000000) (110085193 / 500000000) (Real.log (6381 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6381 / 5120) = -Real.log (5120 / 6381) := by
    rw [show ((6381 / 5120) : ℝ) = ((5120 / 6381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (70686589 / 250000000) ≤ -Real.log (3859 / 5120) ∧
    -Real.log (3859 / 5120) ≤ (282746357 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 8979)) (n := 12)
    (lo := (70686589 / 250000000)) (hi := (282746357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3859) = 1/(3859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-282746357 / 1000000000) (-70686589 / 250000000) (Real.log (3859 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43987057 / 200000000) ≤ -Real.log (10240 / 12759) ∧
    -Real.log (10240 / 12759) ≤ (109967643 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 22999)) (n := 12)
    (lo := (43987057 / 200000000)) (hi := (109967643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12759 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12759 / 10240) = 1/(10240 / 12759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43987057 / 200000000) (109967643 / 500000000) (Real.log (12759 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12759 / 10240) = -Real.log (10240 / 12759) := by
    rw [show ((12759 / 10240) : ℝ) = ((10240 / 12759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28235773 / 100000000) ≤ -Real.log (7721 / 10240) ∧
    -Real.log (7721 / 10240) ≤ (282357731 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 17961)) (n := 12)
    (lo := (28235773 / 100000000)) (hi := (282357731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7721) = 1/(7721 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-282357731 / 1000000000) (-28235773 / 100000000) (Real.log (7721 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (400504909 / 1000000000) ≤ -Real.log (2560 / 3821) ∧
    -Real.log (2560 / 3821) ≤ (40050491 / 100000000) := by
  have h := checkLog_sound (w := (1261 / 6381)) (n := 12)
    (lo := (400504909 / 1000000000)) (hi := (40050491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3821 / 2560) = 1/(2560 / 3821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (400504909 / 1000000000) (40050491 / 100000000) (Real.log (3821 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3821 / 2560) = -Real.log (2560 / 3821) := by
    rw [show ((3821 / 2560) : ℝ) = ((2560 / 3821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16960313 / 25000000) ≤ -Real.log (1299 / 2560) ∧
    -Real.log (1299 / 2560) ≤ (678412521 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 3859)) (n := 12)
    (lo := (16960313 / 25000000)) (hi := (678412521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1299) = 1/(1299 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-678412521 / 1000000000) (-16960313 / 25000000) (Real.log (1299 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (80022453 / 200000000) ≤ -Real.log (5120 / 7639) ∧
    -Real.log (5120 / 7639) ≤ (200056133 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 12759)) (n := 12)
    (lo := (80022453 / 200000000)) (hi := (200056133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7639 / 5120) = 1/(5120 / 7639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (80022453 / 200000000) (200056133 / 500000000) (Real.log (7639 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7639 / 5120) = -Real.log (5120 / 7639) := by
    rw [show ((7639 / 5120) : ℝ) = ((5120 / 7639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (169314613 / 250000000) ≤ -Real.log (2601 / 5120) ∧
    -Real.log (2601 / 5120) ≤ (677258453 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 7721)) (n := 12)
    (lo := (169314613 / 250000000)) (hi := (677258453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2601) = 1/(2601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-677258453 / 1000000000) (-169314613 / 250000000) (Real.log (2601 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9420023 / 31250000) ≤ -Real.log (200000 / 270361) ∧
    -Real.log (200000 / 270361) ≤ (301440737 / 1000000000) := by
  have h := checkLog_sound (w := (70361 / 470361)) (n := 12)
    (lo := (9420023 / 31250000)) (hi := (301440737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270361 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270361 / 200000) = 1/(200000 / 270361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9420023 / 31250000) (301440737 / 1000000000) (Real.log (270361 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (270361 / 200000) = -Real.log (200000 / 270361) := by
    rw [show ((270361 / 200000) : ℝ) = ((200000 / 270361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (433563701 / 1000000000) ≤ -Real.log (129639 / 200000) ∧
    -Real.log (129639 / 200000) ≤ (216781851 / 500000000) := by
  have h := checkLog_sound (w := (70361 / 329639)) (n := 12)
    (lo := (433563701 / 1000000000)) (hi := (216781851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129639) = 1/(129639 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-216781851 / 500000000) (-433563701 / 1000000000) (Real.log (129639 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (150879759 / 500000000) ≤ -Real.log (250000 / 338059) ∧
    -Real.log (250000 / 338059) ≤ (301759519 / 1000000000) := by
  have h := checkLog_sound (w := (88059 / 588059)) (n := 12)
    (lo := (150879759 / 500000000)) (hi := (301759519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338059 / 250000) = 1/(250000 / 338059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (150879759 / 500000000) (301759519 / 1000000000) (Real.log (338059 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (338059 / 250000) = -Real.log (250000 / 338059) := by
    rw [show ((338059 / 250000) : ℝ) = ((250000 / 338059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (217114423 / 500000000) ≤ -Real.log (161941 / 250000) ∧
    -Real.log (161941 / 250000) ≤ (434228847 / 1000000000) := by
  have h := checkLog_sound (w := (88059 / 411941)) (n := 12)
    (lo := (217114423 / 500000000)) (hi := (434228847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161941) = 1/(161941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-434228847 / 1000000000) (-217114423 / 500000000) (Real.log (161941 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45838643 / 200000000) ≤ -Real.log (200000 / 251517) ∧
    -Real.log (200000 / 251517) ≤ (447643 / 1953125) := by
  have h := checkLog_sound (w := (51517 / 451517)) (n := 12)
    (lo := (45838643 / 200000000)) (hi := (447643 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251517 / 200000) = 1/(200000 / 251517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45838643 / 200000000) (447643 / 1953125) (Real.log (251517 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (251517 / 200000) = -Real.log (200000 / 251517) := by
    rw [show ((251517 / 200000) : ℝ) = ((200000 / 251517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74461723 / 250000000) ≤ -Real.log (148483 / 200000) ∧
    -Real.log (148483 / 200000) ≤ (297846893 / 1000000000) := by
  have h := checkLog_sound (w := (51517 / 348483)) (n := 12)
    (lo := (74461723 / 250000000)) (hi := (297846893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148483) = 1/(148483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-297846893 / 1000000000) (-74461723 / 250000000) (Real.log (148483 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229461153 / 1000000000) ≤ -Real.log (500000 / 628961) ∧
    -Real.log (500000 / 628961) ≤ (114730577 / 500000000) := by
  have h := checkLog_sound (w := (128961 / 1128961)) (n := 12)
    (lo := (229461153 / 1000000000)) (hi := (114730577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628961 / 500000) = 1/(500000 / 628961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229461153 / 1000000000) (114730577 / 500000000) (Real.log (628961 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (628961 / 500000) = -Real.log (500000 / 628961) := by
    rw [show ((628961 / 500000) : ℝ) = ((500000 / 628961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7457523 / 25000000) ≤ -Real.log (371039 / 500000) ∧
    -Real.log (371039 / 500000) ≤ (298300921 / 1000000000) := by
  have h := checkLog_sound (w := (128961 / 871039)) (n := 12)
    (lo := (7457523 / 25000000)) (hi := (298300921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371039) = 1/(371039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-298300921 / 1000000000) (-7457523 / 25000000) (Real.log (371039 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (735004437 / 1000000000) ≤ -Real.log (500000000000 / 1042745624387) ∧
    -Real.log (500000000000 / 1042745624387) ≤ (735004439 / 1000000000) := by
  have h := checkLog_sound (w := (42745624387 / 2042745624387)) (n := 12)
    (lo := (41857257 / 1000000000)) (hi := (20928629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1042745624387 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1042745624387 / 1000000000000) = 1/(500000000000 / 1042745624387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (735004437 / 1000000000) (735004439 / 1000000000) (Real.log (1042745624387 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1042745624387 / 500000000000) = -Real.log (500000000000 / 1042745624387) := by
    rw [show ((1042745624387 / 500000000000) : ℝ) = ((500000000000 / 1042745624387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (183997091 / 250000000) ≤ -Real.log (62500000000 / 130471514317) ∧
    -Real.log (62500000000 / 130471514317) ≤ (367994183 / 500000000) := by
  have h := checkLog_sound (w := (5471514317 / 255471514317)) (n := 12)
    (lo := (1338787 / 31250000)) (hi := (8568237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130471514317 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(130471514317 / 125000000000) = 1/(62500000000 / 130471514317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (183997091 / 250000000) (367994183 / 500000000) (Real.log (130471514317 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (130471514317 / 62500000000) = -Real.log (62500000000 / 130471514317) := by
    rw [show ((130471514317 / 62500000000) : ℝ) = ((62500000000 / 130471514317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (131760027 / 250000000) ≤ -Real.log (125000000000 / 211738885933) ∧
    -Real.log (125000000000 / 211738885933) ≤ (527040109 / 1000000000) := by
  have h := checkLog_sound (w := (86738885933 / 336738885933)) (n := 12)
    (lo := (131760027 / 250000000)) (hi := (527040109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211738885933 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211738885933 / 125000000000) = 1/(125000000000 / 211738885933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (131760027 / 250000000) (527040109 / 1000000000) (Real.log (211738885933 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (211738885933 / 125000000000) = -Real.log (125000000000 / 211738885933) := by
    rw [show ((211738885933 / 125000000000) : ℝ) = ((125000000000 / 211738885933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (527762073 / 1000000000) ≤ -Real.log (125000000000 / 211891809217) ∧
    -Real.log (125000000000 / 211891809217) ≤ (263881037 / 500000000) := by
  have h := checkLog_sound (w := (86891809217 / 336891809217)) (n := 12)
    (lo := (527762073 / 1000000000)) (hi := (263881037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211891809217 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211891809217 / 125000000000) = 1/(125000000000 / 211891809217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (527762073 / 1000000000) (263881037 / 500000000) (Real.log (211891809217 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (211891809217 / 125000000000) = -Real.log (125000000000 / 211891809217) := by
    rw [show ((211891809217 / 125000000000) : ℝ) = ((125000000000 / 211891809217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0316

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0317Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0317
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

theorem reflection_log_1_neg : (43987057 / 200000000) ≤ -Real.log (10240 / 12759) ∧
    -Real.log (10240 / 12759) ≤ (109967643 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 22999)) (n := 12)
    (lo := (43987057 / 200000000)) (hi := (109967643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12759 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12759 / 10240) = 1/(10240 / 12759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43987057 / 200000000) (109967643 / 500000000) (Real.log (12759 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12759 / 10240) = -Real.log (10240 / 12759) := by
    rw [show ((12759 / 10240) : ℝ) = ((10240 / 12759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28235773 / 100000000) ≤ -Real.log (7721 / 10240) ∧
    -Real.log (7721 / 10240) ≤ (282357731 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 17961)) (n := 12)
    (lo := (28235773 / 100000000)) (hi := (282357731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7721) = 1/(7721 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-282357731 / 1000000000) (-28235773 / 100000000) (Real.log (7721 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (219700129 / 1000000000) ≤ -Real.log (2560 / 3189) ∧
    -Real.log (2560 / 3189) ≤ (21970013 / 100000000) := by
  have h := checkLog_sound (w := (629 / 5749)) (n := 12)
    (lo := (219700129 / 1000000000)) (hi := (21970013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3189 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3189 / 2560) = 1/(2560 / 3189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (219700129 / 1000000000) (21970013 / 100000000) (Real.log (3189 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3189 / 2560) = -Real.log (2560 / 3189) := by
    rw [show ((3189 / 2560) : ℝ) = ((2560 / 3189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56393851 / 200000000) ≤ -Real.log (1931 / 2560) ∧
    -Real.log (1931 / 2560) ≤ (35246157 / 125000000) := by
  have h := checkLog_sound (w := (629 / 4491)) (n := 12)
    (lo := (56393851 / 200000000)) (hi := (35246157 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1931) = 1/(1931 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-35246157 / 125000000) (-56393851 / 200000000) (Real.log (1931 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (80022453 / 200000000) ≤ -Real.log (5120 / 7639) ∧
    -Real.log (5120 / 7639) ≤ (200056133 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 12759)) (n := 12)
    (lo := (80022453 / 200000000)) (hi := (200056133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7639 / 5120) = 1/(5120 / 7639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (80022453 / 200000000) (200056133 / 500000000) (Real.log (7639 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7639 / 5120) = -Real.log (5120 / 7639) := by
    rw [show ((7639 / 5120) : ℝ) = ((5120 / 7639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (169314613 / 250000000) ≤ -Real.log (2601 / 5120) ∧
    -Real.log (2601 / 5120) ≤ (677258453 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 7721)) (n := 12)
    (lo := (169314613 / 250000000)) (hi := (677258453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2601) = 1/(2601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-677258453 / 1000000000) (-169314613 / 250000000) (Real.log (2601 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199859733 / 500000000) ≤ -Real.log (1280 / 1909) ∧
    -Real.log (1280 / 1909) ≤ (399719467 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 3189)) (n := 12)
    (lo := (199859733 / 500000000)) (hi := (399719467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909 / 1280) = 1/(1280 / 1909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199859733 / 500000000) (399719467 / 1000000000) (Real.log (1909 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1909 / 1280) = -Real.log (1280 / 1909) := by
    rw [show ((1909 / 1280) : ℝ) = ((1280 / 1909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (338052857 / 500000000) ≤ -Real.log (651 / 1280) ∧
    -Real.log (651 / 1280) ≤ (135221143 / 200000000) := by
  have h := checkLog_sound (w := (629 / 1931)) (n := 12)
    (lo := (338052857 / 500000000)) (hi := (135221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 651) = 1/(651 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-135221143 / 200000000) (-338052857 / 500000000) (Real.log (651 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75280833 / 250000000) ≤ -Real.log (62500 / 84461) ∧
    -Real.log (62500 / 84461) ≤ (301123333 / 1000000000) := by
  have h := checkLog_sound (w := (21961 / 146961)) (n := 12)
    (lo := (75280833 / 250000000)) (hi := (301123333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84461 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84461 / 62500) = 1/(62500 / 84461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75280833 / 250000000) (301123333 / 1000000000) (Real.log (84461 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (84461 / 62500) = -Real.log (62500 / 84461) := by
    rw [show ((84461 / 62500) : ℝ) = ((62500 / 84461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (432902083 / 1000000000) ≤ -Real.log (40539 / 62500) ∧
    -Real.log (40539 / 62500) ≤ (108225521 / 250000000) := by
  have h := checkLog_sound (w := (21961 / 103039)) (n := 12)
    (lo := (432902083 / 1000000000)) (hi := (108225521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40539) = 1/(40539 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-108225521 / 250000000) (-432902083 / 1000000000) (Real.log (40539 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75360369 / 250000000) ≤ -Real.log (500000 / 675903) ∧
    -Real.log (500000 / 675903) ≤ (301441477 / 1000000000) := by
  have h := checkLog_sound (w := (175903 / 1175903)) (n := 12)
    (lo := (75360369 / 250000000)) (hi := (301441477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675903 / 500000) = 1/(500000 / 675903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75360369 / 250000000) (301441477 / 1000000000) (Real.log (675903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (675903 / 500000) = -Real.log (500000 / 675903) := by
    rw [show ((675903 / 500000) : ℝ) = ((500000 / 675903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (108391311 / 250000000) ≤ -Real.log (324097 / 500000) ∧
    -Real.log (324097 / 500000) ≤ (86713049 / 200000000) := by
  have h := checkLog_sound (w := (175903 / 824097)) (n := 12)
    (lo := (108391311 / 250000000)) (hi := (86713049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 324097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 324097) = 1/(324097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86713049 / 200000000) (-108391311 / 250000000) (Real.log (324097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45785041 / 200000000) ≤ -Real.log (31250 / 39289) ∧
    -Real.log (31250 / 39289) ≤ (114462603 / 500000000) := by
  have h := checkLog_sound (w := (8039 / 70539)) (n := 12)
    (lo := (45785041 / 200000000)) (hi := (114462603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39289 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39289 / 31250) = 1/(31250 / 39289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45785041 / 200000000) (114462603 / 500000000) (Real.log (39289 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (39289 / 31250) = -Real.log (31250 / 39289) := by
    rw [show ((39289 / 31250) : ℝ) = ((31250 / 39289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297393071 / 1000000000) ≤ -Real.log (23211 / 31250) ∧
    -Real.log (23211 / 31250) ≤ (18587067 / 62500000) := by
  have h := checkLog_sound (w := (8039 / 54461)) (n := 12)
    (lo := (297393071 / 1000000000)) (hi := (18587067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23211) = 1/(23211 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-18587067 / 62500000) (-297393071 / 1000000000) (Real.log (23211 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22919401 / 100000000) ≤ -Real.log (500000 / 628793) ∧
    -Real.log (500000 / 628793) ≤ (229194011 / 1000000000) := by
  have h := checkLog_sound (w := (128793 / 1128793)) (n := 12)
    (lo := (22919401 / 100000000)) (hi := (229194011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628793 / 500000) = 1/(500000 / 628793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22919401 / 100000000) (229194011 / 1000000000) (Real.log (628793 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (628793 / 500000) = -Real.log (500000 / 628793) := by
    rw [show ((628793 / 500000) : ℝ) = ((500000 / 628793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (297848239 / 1000000000) ≤ -Real.log (371207 / 500000) ∧
    -Real.log (371207 / 500000) ≤ (3723103 / 12500000) := by
  have h := checkLog_sound (w := (128793 / 871207)) (n := 12)
    (lo := (297848239 / 1000000000)) (hi := (3723103 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371207) = 1/(371207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3723103 / 12500000) (-297848239 / 1000000000) (Real.log (371207 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (146805083 / 200000000) ≤ -Real.log (250000000000 / 520862626113) ∧
    -Real.log (250000000000 / 520862626113) ≤ (734025417 / 1000000000) := by
  have h := checkLog_sound (w := (20862626113 / 1020862626113)) (n := 12)
    (lo := (8175647 / 200000000)) (hi := (10219559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((520862626113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(520862626113 / 500000000000) = 1/(250000000000 / 520862626113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (146805083 / 200000000) (734025417 / 1000000000) (Real.log (520862626113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (520862626113 / 250000000000) = -Real.log (250000000000 / 520862626113) := by
    rw [show ((520862626113 / 250000000000) : ℝ) = ((250000000000 / 520862626113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (287112 / 390625) ≤ -Real.log (62500000000 / 130343500557) ∧
    -Real.log (62500000000 / 130343500557) ≤ (367503361 / 500000000) := by
  have h := checkLog_sound (w := (5343500557 / 255343500557)) (n := 12)
    (lo := (2092977 / 50000000)) (hi := (41859541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130343500557 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(130343500557 / 125000000000) = 1/(62500000000 / 130343500557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (287112 / 390625) (367503361 / 500000000) (Real.log (130343500557 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (130343500557 / 62500000000) = -Real.log (62500000000 / 130343500557) := by
    rw [show ((130343500557 / 62500000000) : ℝ) = ((62500000000 / 130343500557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (526318277 / 1000000000) ≤ -Real.log (500000000000 / 846344405669) ∧
    -Real.log (500000000000 / 846344405669) ≤ (263159139 / 500000000) := by
  have h := checkLog_sound (w := (346344405669 / 1346344405669)) (n := 12)
    (lo := (526318277 / 1000000000)) (hi := (263159139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846344405669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846344405669 / 500000000000) = 1/(500000000000 / 846344405669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (526318277 / 1000000000) (263159139 / 500000000) (Real.log (846344405669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (846344405669 / 500000000000) = -Real.log (500000000000 / 846344405669) := by
    rw [show ((846344405669 / 500000000000) : ℝ) = ((500000000000 / 846344405669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2108169 / 4000000) ≤ -Real.log (62500000000 / 105869669753) ∧
    -Real.log (62500000000 / 105869669753) ≤ (527042251 / 1000000000) := by
  have h := checkLog_sound (w := (43369669753 / 168369669753)) (n := 12)
    (lo := (2108169 / 4000000)) (hi := (527042251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105869669753 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105869669753 / 62500000000) = 1/(62500000000 / 105869669753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2108169 / 4000000) (527042251 / 1000000000) (Real.log (105869669753 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (105869669753 / 62500000000) = -Real.log (62500000000 / 105869669753) := by
    rw [show ((105869669753 / 62500000000) : ℝ) = ((62500000000 / 105869669753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0317

end


