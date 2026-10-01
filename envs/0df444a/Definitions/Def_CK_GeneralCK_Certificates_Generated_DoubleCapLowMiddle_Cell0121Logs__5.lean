-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0121Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0121Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:57:05.906981+00:00
-- url     : https://prove2.me/theorems/1c51d705-939b-4c92-9d7d-6d459583e3bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0125Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0125Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0125Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0121Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0122Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0123Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0124Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0125Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0121
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

theorem reflection_log_1_neg : (665703717 / 1000000000) ≤ -Real.log (12800 / 24907) ∧
    -Real.log (12800 / 24907) ≤ (332851859 / 500000000) := by
  have h := checkLog_sound (w := (12107 / 37707)) (n := 12)
    (lo := (665703717 / 1000000000)) (hi := (332851859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24907 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24907 / 12800) = 1/(12800 / 24907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (665703717 / 1000000000) (332851859 / 500000000) (Real.log (24907 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24907 / 12800) = -Real.log (12800 / 24907) := by
    rw [show ((24907 / 12800) : ℝ) = ((12800 / 24907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (182260653 / 62500000) ≤ -Real.log (693 / 12800) ∧
    -Real.log (693 / 12800) ≤ (2916170453 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 693) = 1/(693 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2916170453 / 1000000000) (-182260653 / 62500000) (Real.log (693 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26612889 / 40000000) ≤ -Real.log (5120 / 9959) ∧
    -Real.log (5120 / 9959) ≤ (332661113 / 500000000) := by
  have h := checkLog_sound (w := (4839 / 15079)) (n := 12)
    (lo := (26612889 / 40000000)) (hi := (332661113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5120) = 1/(5120 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26612889 / 40000000) (332661113 / 500000000) (Real.log (9959 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9959 / 5120) = -Real.log (5120 / 9959) := by
    rw [show ((9959 / 5120) : ℝ) = ((5120 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1451277523 / 500000000) ≤ -Real.log (281 / 5120) ∧
    -Real.log (281 / 5120) ≤ (2902555051 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 281) = 1/(281 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2902555051 / 1000000000) (-1451277523 / 500000000) (Real.log (281 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (637485807 / 1000000000) ≤ -Real.log (6400 / 12107) ∧
    -Real.log (6400 / 12107) ≤ (39842863 / 62500000) := by
  have h := checkLog_sound (w := (5707 / 18507)) (n := 12)
    (lo := (637485807 / 1000000000)) (hi := (39842863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12107 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12107 / 6400) = 1/(6400 / 12107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (637485807 / 1000000000) (39842863 / 62500000) (Real.log (12107 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12107 / 6400) = -Real.log (6400 / 12107) := by
    rw [show ((12107 / 6400) : ℝ) = ((6400 / 12107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (555755817 / 250000000) ≤ -Real.log (693 / 6400) ∧
    -Real.log (693 / 6400) ≤ (277877909 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 693) = 1/(693 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277877909 / 125000000) (-555755817 / 250000000) (Real.log (693 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (636700829 / 1000000000) ≤ -Real.log (2560 / 4839) ∧
    -Real.log (2560 / 4839) ≤ (63670083 / 100000000) := by
  have h := checkLog_sound (w := (2279 / 7399)) (n := 12)
    (lo := (636700829 / 1000000000)) (hi := (63670083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4839 / 2560) = 1/(2560 / 4839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (636700829 / 1000000000) (63670083 / 100000000) (Real.log (4839 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4839 / 2560) = -Real.log (2560 / 4839) := by
    rw [show ((4839 / 2560) : ℝ) = ((2560 / 4839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1104703933 / 500000000) ≤ -Real.log (281 / 2560) ∧
    -Real.log (281 / 2560) ≤ (220940787 / 100000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 281) = 1/(281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-220940787 / 100000000) (-1104703933 / 500000000) (Real.log (281 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (670739493 / 1000000000) ≤ -Real.log (1000000 / 1955683) ∧
    -Real.log (1000000 / 1955683) ≤ (335369747 / 500000000) := by
  have h := checkLog_sound (w := (955683 / 2955683)) (n := 12)
    (lo := (670739493 / 1000000000)) (hi := (335369747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1955683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1955683 / 1000000) = 1/(1000000 / 1955683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (670739493 / 1000000000) (335369747 / 500000000) (Real.log (1955683 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1955683 / 1000000) = -Real.log (1000000 / 1955683) := by
    rw [show ((1955683 / 1000000) : ℝ) = ((1000000 / 1955683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1558193463 / 500000000) ≤ -Real.log (44317 / 1000000) ∧
    -Real.log (44317 / 1000000) ≤ (3116386931 / 1000000000) := by
  have h := checkLog_sound (w := (18183 / 106817)) (n := 12)
    (lo := (171899103 / 500000000)) (hi := (343798207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44317) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 44317) = 1/(44317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3116386931 / 1000000000) (-1558193463 / 500000000) (Real.log (44317 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134205057 / 200000000) ≤ -Real.log (500000 / 978121) ∧
    -Real.log (500000 / 978121) ≤ (335512643 / 500000000) := by
  have h := checkLog_sound (w := (478121 / 1478121)) (n := 12)
    (lo := (134205057 / 200000000)) (hi := (335512643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978121 / 500000) = 1/(500000 / 978121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134205057 / 200000000) (335512643 / 500000000) (Real.log (978121 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (978121 / 500000) = -Real.log (500000 / 978121) := by
    rw [show ((978121 / 500000) : ℝ) = ((500000 / 978121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3129080823 / 1000000000) ≤ -Real.log (21879 / 500000) ∧
    -Real.log (21879 / 500000) ≤ (782270207 / 250000000) := by
  have h := checkLog_sound (w := (9371 / 53129)) (n := 12)
    (lo := (356492103 / 1000000000)) (hi := (44561513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21879) = 1/(21879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-782270207 / 250000000) (-3129080823 / 1000000000) (Real.log (21879 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167608929 / 250000000) ≤ -Real.log (1000000 / 1955089) ∧
    -Real.log (1000000 / 1955089) ≤ (670435717 / 1000000000) := by
  have h := checkLog_sound (w := (955089 / 2955089)) (n := 12)
    (lo := (167608929 / 250000000)) (hi := (670435717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1955089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1955089 / 1000000) = 1/(1000000 / 1955089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167608929 / 250000000) (670435717 / 1000000000) (Real.log (1955089 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1955089 / 1000000) = -Real.log (1000000 / 1955089) := by
    rw [show ((1955089 / 1000000) : ℝ) = ((1000000 / 1955089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3103072523 / 1000000000) ≤ -Real.log (44911 / 1000000) ∧
    -Real.log (44911 / 1000000) ≤ (193942033 / 62500000) := by
  have h := checkLog_sound (w := (17589 / 107411)) (n := 12)
    (lo := (330483803 / 1000000000)) (hi := (82620951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 44911) = 1/(44911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-193942033 / 62500000) (-3103072523 / 1000000000) (Real.log (44911 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1676827 / 2500000) ≤ -Real.log (500000 / 977833) ∧
    -Real.log (500000 / 977833) ≤ (670730801 / 1000000000) := by
  have h := checkLog_sound (w := (477833 / 1477833)) (n := 12)
    (lo := (1676827 / 2500000)) (hi := (670730801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977833 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977833 / 500000) = 1/(500000 / 977833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1676827 / 2500000) (670730801 / 1000000000) (Real.log (977833 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (977833 / 500000) = -Real.log (500000 / 977833) := by
    rw [show ((977833 / 500000) : ℝ) = ((500000 / 977833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3116003399 / 1000000000) ≤ -Real.log (22167 / 500000) ∧
    -Real.log (22167 / 500000) ≤ (779000851 / 250000000) := by
  have h := checkLog_sound (w := (9083 / 53417)) (n := 12)
    (lo := (343414679 / 1000000000)) (hi := (8585367 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22167) = 1/(22167 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-779000851 / 250000000) (-3116003399 / 1000000000) (Real.log (22167 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1893563209 / 500000000) ≤ -Real.log (10000000000 / 441294085791) ∧
    -Real.log (10000000000 / 441294085791) ≤ (473390803 / 125000000) := by
  have h := checkLog_sound (w := (121294085791 / 761294085791)) (n := 12)
    (lo := (160695259 / 500000000)) (hi := (321390519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441294085791 / 320000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(441294085791 / 320000000000) = 1/(10000000000 / 441294085791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1893563209 / 500000000) (473390803 / 125000000) (Real.log (441294085791 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (441294085791 / 10000000000) = -Real.log (10000000000 / 441294085791) := by
    rw [show ((441294085791 / 10000000000) : ℝ) = ((10000000000 / 441294085791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (950026527 / 250000000) ≤ -Real.log (100000000000 / 4470592805887) ∧
    -Real.log (100000000000 / 4470592805887) ≤ (1900053057 / 500000000) := by
  have h := checkLog_sound (w := (1270592805887 / 7670592805887)) (n := 12)
    (lo := (10449069 / 31250000)) (hi := (334370209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4470592805887 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4470592805887 / 3200000000000) = 1/(100000000000 / 4470592805887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (950026527 / 250000000) (1900053057 / 500000000) (Real.log (4470592805887 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4470592805887 / 100000000000) = -Real.log (100000000000 / 4470592805887) := by
    rw [show ((4470592805887 / 100000000000) : ℝ) = ((100000000000 / 4470592805887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3773508239 / 1000000000) ≤ -Real.log (250000000000 / 10883129968159) ∧
    -Real.log (250000000000 / 10883129968159) ≤ (754701649 / 200000000) := by
  have h := checkLog_sound (w := (2883129968159 / 18883129968159)) (n := 12)
    (lo := (307772339 / 1000000000)) (hi := (15388617 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10883129968159 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10883129968159 / 8000000000000) = 1/(250000000000 / 10883129968159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3773508239 / 1000000000) (754701649 / 200000000) (Real.log (10883129968159 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10883129968159 / 250000000000) = -Real.log (250000000000 / 10883129968159) := by
    rw [show ((10883129968159 / 250000000000) : ℝ) = ((250000000000 / 10883129968159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3786734199 / 1000000000) ≤ -Real.log (100000000000 / 4411210357739) ∧
    -Real.log (100000000000 / 4411210357739) ≤ (757346841 / 200000000) := by
  have h := checkLog_sound (w := (1211210357739 / 7611210357739)) (n := 12)
    (lo := (320998299 / 1000000000)) (hi := (3209983 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4411210357739 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4411210357739 / 3200000000000) = 1/(100000000000 / 4411210357739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3786734199 / 1000000000) (757346841 / 200000000) (Real.log (4411210357739 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4411210357739 / 100000000000) = -Real.log (100000000000 / 4411210357739) := by
    rw [show ((4411210357739 / 100000000000) : ℝ) = ((100000000000 / 4411210357739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0121

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0122
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

theorem reflection_log_1_neg : (26612889 / 40000000) ≤ -Real.log (5120 / 9959) ∧
    -Real.log (5120 / 9959) ≤ (332661113 / 500000000) := by
  have h := checkLog_sound (w := (4839 / 15079)) (n := 12)
    (lo := (26612889 / 40000000)) (hi := (332661113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5120) = 1/(5120 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26612889 / 40000000) (332661113 / 500000000) (Real.log (9959 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9959 / 5120) = -Real.log (5120 / 9959) := by
    rw [show ((9959 / 5120) : ℝ) = ((5120 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1451277523 / 500000000) ≤ -Real.log (281 / 5120) ∧
    -Real.log (281 / 5120) ≤ (2902555051 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 281) = 1/(281 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2902555051 / 1000000000) (-1451277523 / 500000000) (Real.log (281 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166235147 / 250000000) ≤ -Real.log (1600 / 3111) ∧
    -Real.log (1600 / 3111) ≤ (664940589 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 4711)) (n := 12)
    (lo := (166235147 / 250000000)) (hi := (664940589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 1600) = 1/(1600 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166235147 / 250000000) (664940589 / 1000000000) (Real.log (3111 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3111 / 1600) = -Real.log (1600 / 3111) := by
    rw [show ((3111 / 1600) : ℝ) = ((1600 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (361140317 / 125000000) ≤ -Real.log (89 / 1600) ∧
    -Real.log (89 / 1600) ≤ (2889122541 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 89) = 1/(89 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2889122541 / 1000000000) (-361140317 / 125000000) (Real.log (89 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (636700829 / 1000000000) ≤ -Real.log (2560 / 4839) ∧
    -Real.log (2560 / 4839) ≤ (63670083 / 100000000) := by
  have h := checkLog_sound (w := (2279 / 7399)) (n := 12)
    (lo := (636700829 / 1000000000)) (hi := (63670083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4839 / 2560) = 1/(2560 / 4839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (636700829 / 1000000000) (63670083 / 100000000) (Real.log (4839 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4839 / 2560) = -Real.log (2560 / 4839) := by
    rw [show ((4839 / 2560) : ℝ) = ((2560 / 4839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1104703933 / 500000000) ≤ -Real.log (281 / 2560) ∧
    -Real.log (281 / 2560) ≤ (220940787 / 100000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 281) = 1/(281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-220940787 / 100000000) (-1104703933 / 500000000) (Real.log (281 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317957617 / 500000000) ≤ -Real.log (800 / 1511) ∧
    -Real.log (800 / 1511) ≤ (127183047 / 200000000) := by
  have h := checkLog_sound (w := (711 / 2311)) (n := 12)
    (lo := (317957617 / 500000000)) (hi := (127183047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 800) = 1/(800 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317957617 / 500000000) (127183047 / 200000000) (Real.log (1511 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1511 / 800) = -Real.log (800 / 1511) := by
    rw [show ((1511 / 800) : ℝ) = ((800 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (548993839 / 250000000) ≤ -Real.log (89 / 800) ∧
    -Real.log (89 / 800) ≤ (6862423 / 3125000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 89) = 1/(89 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6862423 / 3125000) (-548993839 / 250000000) (Real.log (89 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67045413 / 100000000) ≤ -Real.log (8000 / 15641) ∧
    -Real.log (8000 / 15641) ≤ (670454131 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 23641)) (n := 12)
    (lo := (67045413 / 100000000)) (hi := (670454131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15641 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15641 / 8000) = 1/(8000 / 15641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67045413 / 100000000) (670454131 / 1000000000) (Real.log (15641 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (15641 / 8000) = -Real.log (8000 / 15641) := by
    rw [show ((15641 / 8000) : ℝ) = ((8000 / 15641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3103874429 / 1000000000) ≤ -Real.log (359 / 8000) ∧
    -Real.log (359 / 8000) ≤ (1551937217 / 500000000) := by
  have h := checkLog_sound (w := (141 / 859)) (n := 12)
    (lo := (331285709 / 1000000000)) (hi := (33128571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 359) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(500 / 359) = 1/(359 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1551937217 / 500000000) (-3103874429 / 1000000000) (Real.log (359 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167685001 / 250000000) ≤ -Real.log (250000 / 488921) ∧
    -Real.log (250000 / 488921) ≤ (134148001 / 200000000) := by
  have h := checkLog_sound (w := (238921 / 738921)) (n := 12)
    (lo := (167685001 / 250000000)) (hi := (134148001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488921 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488921 / 250000) = 1/(250000 / 488921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167685001 / 250000000) (134148001 / 200000000) (Real.log (488921 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (488921 / 250000) = -Real.log (250000 / 488921) := by
    rw [show ((488921 / 250000) : ℝ) = ((250000 / 488921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3116409491 / 1000000000) ≤ -Real.log (11079 / 250000) ∧
    -Real.log (11079 / 250000) ≤ (389551187 / 125000000) := by
  have h := checkLog_sound (w := (2273 / 13352)) (n := 12)
    (lo := (343820771 / 1000000000)) (hi := (85955193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11079) = 1/(11079 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-389551187 / 125000000) (-3116409491 / 1000000000) (Real.log (11079 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (670141057 / 1000000000) ≤ -Real.log (1000000 / 1954513) ∧
    -Real.log (1000000 / 1954513) ≤ (335070529 / 500000000) := by
  have h := checkLog_sound (w := (954513 / 2954513)) (n := 12)
    (lo := (670141057 / 1000000000)) (hi := (335070529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954513 / 1000000) = 1/(1000000 / 1954513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (670141057 / 1000000000) (335070529 / 500000000) (Real.log (1954513 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1954513 / 1000000) = -Real.log (1000000 / 1954513) := by
    rw [show ((1954513 / 1000000) : ℝ) = ((1000000 / 1954513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (618065741 / 200000000) ≤ -Real.log (45487 / 1000000) ∧
    -Real.log (45487 / 1000000) ≤ (309032871 / 100000000) := by
  have h := checkLog_sound (w := (17013 / 107987)) (n := 12)
    (lo := (63547997 / 200000000)) (hi := (158869993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45487) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45487) = 1/(45487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-309032871 / 100000000) (-618065741 / 200000000) (Real.log (45487 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (167609057 / 250000000) ≤ -Real.log (100000 / 195509) ∧
    -Real.log (100000 / 195509) ≤ (670436229 / 1000000000) := by
  have h := checkLog_sound (w := (95509 / 295509)) (n := 12)
    (lo := (167609057 / 250000000)) (hi := (670436229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195509 / 100000) = 1/(100000 / 195509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (167609057 / 250000000) (670436229 / 1000000000) (Real.log (195509 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (195509 / 100000) = -Real.log (100000 / 195509) := by
    rw [show ((195509 / 100000) : ℝ) = ((100000 / 195509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3103094789 / 1000000000) ≤ -Real.log (4491 / 100000) ∧
    -Real.log (4491 / 100000) ≤ (1551547397 / 500000000) := by
  have h := checkLog_sound (w := (1759 / 10741)) (n := 12)
    (lo := (330506069 / 1000000000)) (hi := (33050607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4491) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4491) = 1/(4491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1551547397 / 500000000) (-3103094789 / 1000000000) (Real.log (4491 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3774328559 / 1000000000) ≤ -Real.log (250000000000 / 10892061281337) ∧
    -Real.log (250000000000 / 10892061281337) ≤ (754865713 / 200000000) := by
  have h := checkLog_sound (w := (2892061281337 / 18892061281337)) (n := 12)
    (lo := (308592659 / 1000000000)) (hi := (15429633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10892061281337 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10892061281337 / 8000000000000) = 1/(250000000000 / 10892061281337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3774328559 / 1000000000) (754865713 / 200000000) (Real.log (10892061281337 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10892061281337 / 250000000000) = -Real.log (250000000000 / 10892061281337) := by
    rw [show ((10892061281337 / 250000000000) : ℝ) = ((250000000000 / 10892061281337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1893574747 / 500000000) ≤ -Real.log (12500000000 / 551630336673) ∧
    -Real.log (12500000000 / 551630336673) ≤ (7574299 / 2000000) := by
  have h := checkLog_sound (w := (151630336673 / 951630336673)) (n := 12)
    (lo := (160706797 / 500000000)) (hi := (64282719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((551630336673 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(551630336673 / 400000000000) = 1/(12500000000 / 551630336673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1893574747 / 500000000) (7574299 / 2000000) (Real.log (551630336673 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (551630336673 / 12500000000) = -Real.log (12500000000 / 551630336673) := by
    rw [show ((551630336673 / 12500000000) : ℝ) = ((12500000000 / 551630336673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1880234881 / 500000000) ≤ -Real.log (500000000000 / 21484303207509) ∧
    -Real.log (500000000000 / 21484303207509) ≤ (470058721 / 125000000) := by
  have h := checkLog_sound (w := (5484303207509 / 37484303207509)) (n := 12)
    (lo := (147366931 / 500000000)) (hi := (294733863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21484303207509 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21484303207509 / 16000000000000) = 1/(500000000000 / 21484303207509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1880234881 / 500000000) (470058721 / 125000000) (Real.log (21484303207509 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (21484303207509 / 500000000000) = -Real.log (500000000000 / 21484303207509) := by
    rw [show ((21484303207509 / 500000000000) : ℝ) = ((500000000000 / 21484303207509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3773531017 / 1000000000) ≤ -Real.log (50000000000 / 2176675573369) ∧
    -Real.log (50000000000 / 2176675573369) ≤ (3773531023 / 1000000000) := by
  have h := checkLog_sound (w := (576675573369 / 3776675573369)) (n := 12)
    (lo := (307795117 / 1000000000)) (hi := (153897559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2176675573369 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2176675573369 / 1600000000000) = 1/(50000000000 / 2176675573369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3773531017 / 1000000000) (3773531023 / 1000000000) (Real.log (2176675573369 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2176675573369 / 50000000000) = -Real.log (50000000000 / 2176675573369) := by
    rw [show ((2176675573369 / 50000000000) : ℝ) = ((50000000000 / 2176675573369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0122

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0123Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0123
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

theorem reflection_log_1_neg : (166235147 / 250000000) ≤ -Real.log (1600 / 3111) ∧
    -Real.log (1600 / 3111) ≤ (664940589 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 4711)) (n := 12)
    (lo := (166235147 / 250000000)) (hi := (664940589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 1600) = 1/(1600 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166235147 / 250000000) (664940589 / 1000000000) (Real.log (3111 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3111 / 1600) = -Real.log (1600 / 3111) := by
    rw [show ((3111 / 1600) : ℝ) = ((1600 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (361140317 / 125000000) ≤ -Real.log (89 / 1600) ∧
    -Real.log (89 / 1600) ≤ (2889122541 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 89) = 1/(89 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2889122541 / 1000000000) (-361140317 / 125000000) (Real.log (89 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132911761 / 200000000) ≤ -Real.log (25600 / 49757) ∧
    -Real.log (25600 / 49757) ≤ (332279403 / 500000000) := by
  have h := checkLog_sound (w := (24157 / 75357)) (n := 12)
    (lo := (132911761 / 200000000)) (hi := (332279403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49757 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49757 / 25600) = 1/(25600 / 49757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132911761 / 200000000) (332279403 / 500000000) (Real.log (49757 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49757 / 25600) = -Real.log (25600 / 49757) := by
    rw [show ((49757 / 25600) : ℝ) = ((25600 / 49757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2875868069 / 1000000000) ≤ -Real.log (1443 / 25600) ∧
    -Real.log (1443 / 25600) ≤ (1437934037 / 500000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1443) = 1/(1443 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1437934037 / 500000000) (-2875868069 / 1000000000) (Real.log (1443 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317957617 / 500000000) ≤ -Real.log (800 / 1511) ∧
    -Real.log (800 / 1511) ≤ (127183047 / 200000000) := by
  have h := checkLog_sound (w := (711 / 2311)) (n := 12)
    (lo := (317957617 / 500000000)) (hi := (127183047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 800) = 1/(800 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317957617 / 500000000) (127183047 / 200000000) (Real.log (1511 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1511 / 800) = -Real.log (800 / 1511) := by
    rw [show ((1511 / 800) : ℝ) = ((800 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (548993839 / 250000000) ≤ -Real.log (89 / 800) ∧
    -Real.log (89 / 800) ≤ (6862423 / 3125000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 89) = 1/(89 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6862423 / 3125000) (-548993839 / 250000000) (Real.log (89 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317564511 / 500000000) ≤ -Real.log (12800 / 24157) ∧
    -Real.log (12800 / 24157) ≤ (635129023 / 1000000000) := by
  have h := checkLog_sound (w := (11357 / 36957)) (n := 12)
    (lo := (317564511 / 500000000)) (hi := (635129023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24157 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24157 / 12800) = 1/(12800 / 24157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317564511 / 500000000) (635129023 / 1000000000) (Real.log (24157 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24157 / 12800) = -Real.log (12800 / 24157) := by
    rw [show ((24157 / 12800) : ℝ) = ((12800 / 24157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2182720889 / 1000000000) ≤ -Real.log (1443 / 12800) ∧
    -Real.log (1443 / 12800) ≤ (2182720893 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1443) = 1/(1443 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2182720893 / 1000000000) (-2182720889 / 1000000000) (Real.log (1443 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167542427 / 250000000) ≤ -Real.log (1000000 / 1954569) ∧
    -Real.log (1000000 / 1954569) ≤ (670169709 / 1000000000) := by
  have h := checkLog_sound (w := (954569 / 2954569)) (n := 12)
    (lo := (167542427 / 250000000)) (hi := (670169709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954569 / 1000000) = 1/(1000000 / 1954569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167542427 / 250000000) (670169709 / 1000000000) (Real.log (1954569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1954569 / 1000000) = -Real.log (1000000 / 1954569) := by
    rw [show ((1954569 / 1000000) : ℝ) = ((1000000 / 1954569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (618312117 / 200000000) ≤ -Real.log (45431 / 1000000) ∧
    -Real.log (45431 / 1000000) ≤ (309156059 / 100000000) := by
  have h := checkLog_sound (w := (17069 / 107931)) (n := 12)
    (lo := (63794373 / 200000000)) (hi := (159485933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45431) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45431) = 1/(45431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-309156059 / 100000000) (-618312117 / 200000000) (Real.log (45431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (670454641 / 1000000000) ≤ -Real.log (500000 / 977563) ∧
    -Real.log (500000 / 977563) ≤ (335227321 / 500000000) := by
  have h := checkLog_sound (w := (477563 / 1477563)) (n := 12)
    (lo := (670454641 / 1000000000)) (hi := (335227321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977563 / 500000) = 1/(500000 / 977563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (670454641 / 1000000000) (335227321 / 500000000) (Real.log (977563 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (977563 / 500000) = -Real.log (500000 / 977563) := by
    rw [show ((977563 / 500000) : ℝ) = ((500000 / 977563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1551948357 / 500000000) ≤ -Real.log (22437 / 500000) ∧
    -Real.log (22437 / 500000) ≤ (3103896719 / 1000000000) := by
  have h := checkLog_sound (w := (8813 / 53687)) (n := 12)
    (lo := (165653997 / 500000000)) (hi := (66261599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22437) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22437) = 1/(22437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3103896719 / 1000000000) (-1551948357 / 500000000) (Real.log (22437 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (669846823 / 1000000000) ≤ -Real.log (500000 / 976969) ∧
    -Real.log (500000 / 976969) ≤ (83730853 / 125000000) := by
  have h := checkLog_sound (w := (476969 / 1476969)) (n := 12)
    (lo := (669846823 / 1000000000)) (hi := (83730853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976969 / 500000) = 1/(500000 / 976969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (669846823 / 1000000000) (83730853 / 125000000) (Real.log (976969 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (976969 / 500000) = -Real.log (500000 / 976969) := by
    rw [show ((976969 / 500000) : ℝ) = ((500000 / 976969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3077766961 / 1000000000) ≤ -Real.log (23031 / 500000) ∧
    -Real.log (23031 / 500000) ≤ (1538883483 / 500000000) := by
  have h := checkLog_sound (w := (8219 / 54281)) (n := 12)
    (lo := (305178241 / 1000000000)) (hi := (152589121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 23031) = 1/(23031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1538883483 / 500000000) (-3077766961 / 1000000000) (Real.log (23031 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (670141569 / 1000000000) ≤ -Real.log (500000 / 977257) ∧
    -Real.log (500000 / 977257) ≤ (67014157 / 100000000) := by
  have h := checkLog_sound (w := (477257 / 1477257)) (n := 12)
    (lo := (670141569 / 1000000000)) (hi := (67014157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977257 / 500000) = 1/(500000 / 977257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (670141569 / 1000000000) (67014157 / 100000000) (Real.log (977257 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (977257 / 500000) = -Real.log (500000 / 977257) := by
    rw [show ((977257 / 500000) : ℝ) = ((500000 / 977257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (309035069 / 100000000) ≤ -Real.log (22743 / 500000) ∧
    -Real.log (22743 / 500000) ≤ (618070139 / 200000000) := by
  have h := checkLog_sound (w := (8507 / 53993)) (n := 12)
    (lo := (31776197 / 100000000)) (hi := (317761971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22743) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22743) = 1/(22743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-618070139 / 200000000) (-309035069 / 100000000) (Real.log (22743 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3761730293 / 1000000000) ≤ -Real.log (500000000000 / 21511401906187) ∧
    -Real.log (500000000000 / 21511401906187) ≤ (3761730299 / 1000000000) := by
  have h := checkLog_sound (w := (5511401906187 / 37511401906187)) (n := 12)
    (lo := (295994393 / 1000000000)) (hi := (147997197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21511401906187 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21511401906187 / 16000000000000) = 1/(500000000000 / 21511401906187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3761730293 / 1000000000) (3761730299 / 1000000000) (Real.log (21511401906187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21511401906187 / 500000000000) = -Real.log (500000000000 / 21511401906187) := by
    rw [show ((21511401906187 / 500000000000) : ℝ) = ((500000000000 / 21511401906187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (754870271 / 200000000) ≤ -Real.log (500000000000 / 21784619155859) ∧
    -Real.log (500000000000 / 21784619155859) ≤ (3774351361 / 1000000000) := by
  have h := checkLog_sound (w := (5784619155859 / 37784619155859)) (n := 12)
    (lo := (61723091 / 200000000)) (hi := (9644233 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21784619155859 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21784619155859 / 16000000000000) = 1/(500000000000 / 21784619155859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (754870271 / 200000000) (3774351361 / 1000000000) (Real.log (21784619155859 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21784619155859 / 500000000000) = -Real.log (500000000000 / 21784619155859) := by
    rw [show ((21784619155859 / 500000000000) : ℝ) = ((500000000000 / 21784619155859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (468451723 / 125000000) ≤ -Real.log (250000000000 / 10604934653293) ∧
    -Real.log (250000000000 / 10604934653293) ≤ (374761379 / 100000000) := by
  have h := checkLog_sound (w := (2604934653293 / 18604934653293)) (n := 12)
    (lo := (70469471 / 250000000)) (hi := (56375577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10604934653293 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10604934653293 / 8000000000000) = 1/(250000000000 / 10604934653293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (468451723 / 125000000) (374761379 / 100000000) (Real.log (10604934653293 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10604934653293 / 250000000000) = -Real.log (250000000000 / 10604934653293) := by
    rw [show ((10604934653293 / 250000000000) : ℝ) = ((250000000000 / 10604934653293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3760492259 / 1000000000) ≤ -Real.log (500000000000 / 21484786527723) ∧
    -Real.log (500000000000 / 21484786527723) ≤ (752098453 / 200000000) := by
  have h := checkLog_sound (w := (5484786527723 / 37484786527723)) (n := 12)
    (lo := (294756359 / 1000000000)) (hi := (7368909 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21484786527723 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21484786527723 / 16000000000000) = 1/(500000000000 / 21484786527723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3760492259 / 1000000000) (752098453 / 200000000) (Real.log (21484786527723 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21484786527723 / 500000000000) = -Real.log (500000000000 / 21484786527723) := by
    rw [show ((21484786527723 / 500000000000) : ℝ) = ((500000000000 / 21484786527723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0123

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0124Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0124
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

theorem reflection_log_1_neg : (132911761 / 200000000) ≤ -Real.log (25600 / 49757) ∧
    -Real.log (25600 / 49757) ≤ (332279403 / 500000000) := by
  have h := checkLog_sound (w := (24157 / 75357)) (n := 12)
    (lo := (132911761 / 200000000)) (hi := (332279403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49757 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49757 / 25600) = 1/(25600 / 49757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132911761 / 200000000) (332279403 / 500000000) (Real.log (49757 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49757 / 25600) = -Real.log (25600 / 49757) := by
    rw [show ((49757 / 25600) : ℝ) = ((25600 / 49757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2875868069 / 1000000000) ≤ -Real.log (1443 / 25600) ∧
    -Real.log (1443 / 25600) ≤ (1437934037 / 500000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1443) = 1/(1443 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1437934037 / 500000000) (-2875868069 / 1000000000) (Real.log (1443 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166044219 / 250000000) ≤ -Real.log (12800 / 24869) ∧
    -Real.log (12800 / 24869) ≤ (664176877 / 1000000000) := by
  have h := checkLog_sound (w := (12069 / 37669)) (n := 12)
    (lo := (166044219 / 250000000)) (hi := (664176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24869 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24869 / 12800) = 1/(12800 / 24869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166044219 / 250000000) (664176877 / 1000000000) (Real.log (24869 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24869 / 12800) = -Real.log (12800 / 24869) := by
    rw [show ((24869 / 12800) : ℝ) = ((12800 / 24869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2862786987 / 1000000000) ≤ -Real.log (731 / 12800) ∧
    -Real.log (731 / 12800) ≤ (178924187 / 62500000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 731) = 1/(731 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-178924187 / 62500000) (-2862786987 / 1000000000) (Real.log (731 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317564511 / 500000000) ≤ -Real.log (12800 / 24157) ∧
    -Real.log (12800 / 24157) ≤ (635129023 / 1000000000) := by
  have h := checkLog_sound (w := (11357 / 36957)) (n := 12)
    (lo := (317564511 / 500000000)) (hi := (635129023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24157 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24157 / 12800) = 1/(12800 / 24157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317564511 / 500000000) (635129023 / 1000000000) (Real.log (24157 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24157 / 12800) = -Real.log (12800 / 24157) := by
    rw [show ((24157 / 12800) : ℝ) = ((12800 / 24157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2182720889 / 1000000000) ≤ -Real.log (1443 / 12800) ∧
    -Real.log (1443 / 12800) ≤ (2182720893 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1443) = 1/(1443 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2182720893 / 1000000000) (-2182720889 / 1000000000) (Real.log (1443 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (634342191 / 1000000000) ≤ -Real.log (6400 / 12069) ∧
    -Real.log (6400 / 12069) ≤ (39646387 / 62500000) := by
  have h := checkLog_sound (w := (5669 / 18469)) (n := 12)
    (lo := (634342191 / 1000000000)) (hi := (39646387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12069 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12069 / 6400) = 1/(6400 / 12069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (634342191 / 1000000000) (39646387 / 62500000) (Real.log (12069 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12069 / 6400) = -Real.log (6400 / 12069) := by
    rw [show ((12069 / 6400) : ℝ) = ((6400 / 12069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2169639807 / 1000000000) ≤ -Real.log (731 / 6400) ∧
    -Real.log (731 / 6400) ≤ (2169639811 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 731) = 1/(731 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2169639811 / 1000000000) (-2169639807 / 1000000000) (Real.log (731 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (334942603 / 500000000) ≤ -Real.log (1000000 / 1954013) ∧
    -Real.log (1000000 / 1954013) ≤ (669885207 / 1000000000) := by
  have h := checkLog_sound (w := (954013 / 2954013)) (n := 12)
    (lo := (334942603 / 500000000)) (hi := (669885207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954013 / 1000000) = 1/(1000000 / 1954013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (334942603 / 500000000) (669885207 / 1000000000) (Real.log (1954013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1954013 / 1000000) = -Real.log (1000000 / 1954013) := by
    rw [show ((1954013 / 1000000) : ℝ) = ((1000000 / 1954013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192462283 / 62500000) ≤ -Real.log (45987 / 1000000) ∧
    -Real.log (45987 / 1000000) ≤ (3079396533 / 1000000000) := by
  have h := checkLog_sound (w := (16513 / 108487)) (n := 12)
    (lo := (599234 / 1953125)) (hi := (306807809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45987) = 1/(45987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3079396533 / 1000000000) (-192462283 / 62500000) (Real.log (45987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33508511 / 50000000) ≤ -Real.log (100000 / 195457) ∧
    -Real.log (100000 / 195457) ≤ (670170221 / 1000000000) := by
  have h := checkLog_sound (w := (95457 / 295457)) (n := 12)
    (lo := (33508511 / 50000000)) (hi := (670170221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195457 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195457 / 100000) = 1/(100000 / 195457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33508511 / 50000000) (670170221 / 1000000000) (Real.log (195457 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (195457 / 100000) = -Real.log (100000 / 195457) := by
    rw [show ((195457 / 100000) : ℝ) = ((100000 / 195457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (772895649 / 250000000) ≤ -Real.log (4543 / 100000) ∧
    -Real.log (4543 / 100000) ≤ (3091582601 / 1000000000) := by
  have h := checkLog_sound (w := (1707 / 10793)) (n := 12)
    (lo := (79748469 / 250000000)) (hi := (318993877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4543) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4543) = 1/(4543 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3091582601 / 1000000000) (-772895649 / 250000000) (Real.log (4543 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (334776507 / 500000000) ≤ -Real.log (250000 / 488341) ∧
    -Real.log (250000 / 488341) ≤ (133910603 / 200000000) := by
  have h := checkLog_sound (w := (238341 / 738341)) (n := 12)
    (lo := (334776507 / 500000000)) (hi := (133910603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488341 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488341 / 250000) = 1/(250000 / 488341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (334776507 / 500000000) (133910603 / 200000000) (Real.log (488341 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (488341 / 250000) = -Real.log (250000 / 488341) := by
    rw [show ((488341 / 250000) : ℝ) = ((250000 / 488341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3065382501 / 1000000000) ≤ -Real.log (11659 / 250000) ∧
    -Real.log (11659 / 250000) ≤ (1532691253 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 13642)) (n := 12)
    (lo := (292793781 / 1000000000)) (hi := (146396891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11659) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11659) = 1/(11659 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1532691253 / 500000000) (-3065382501 / 1000000000) (Real.log (11659 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (133969467 / 200000000) ≤ -Real.log (1000000 / 1953939) ∧
    -Real.log (1000000 / 1953939) ≤ (83730917 / 125000000) := by
  have h := checkLog_sound (w := (953939 / 2953939)) (n := 12)
    (lo := (133969467 / 200000000)) (hi := (83730917 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953939 / 1000000) = 1/(1000000 / 1953939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (133969467 / 200000000) (83730917 / 125000000) (Real.log (1953939 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1953939 / 1000000) = -Real.log (1000000 / 1953939) := by
    rw [show ((1953939 / 1000000) : ℝ) = ((1000000 / 1953939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3077788671 / 1000000000) ≤ -Real.log (46061 / 1000000) ∧
    -Real.log (46061 / 1000000) ≤ (769447169 / 250000000) := by
  have h := checkLog_sound (w := (16439 / 108561)) (n := 12)
    (lo := (305199951 / 1000000000)) (hi := (19074997 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46061) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 46061) = 1/(46061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-769447169 / 250000000) (-3077788671 / 1000000000) (Real.log (46061 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1874640867 / 500000000) ≤ -Real.log (62500000000 / 2655659479853) ∧
    -Real.log (62500000000 / 2655659479853) ≤ (187464087 / 50000000) := by
  have h := checkLog_sound (w := (655659479853 / 4655659479853)) (n := 12)
    (lo := (141772917 / 500000000)) (hi := (56709167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2655659479853 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2655659479853 / 2000000000000) = 1/(62500000000 / 2655659479853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1874640867 / 500000000) (187464087 / 50000000) (Real.log (2655659479853 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2655659479853 / 62500000000) = -Real.log (62500000000 / 2655659479853) := by
    rw [show ((2655659479853 / 62500000000) : ℝ) = ((62500000000 / 2655659479853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (235109551 / 62500000) ≤ -Real.log (500000000000 / 21511886418667) ∧
    -Real.log (500000000000 / 21511886418667) ≤ (1880876411 / 500000000) := by
  have h := checkLog_sound (w := (5511886418667 / 37511886418667)) (n := 12)
    (lo := (74004229 / 250000000)) (hi := (296016917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21511886418667 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21511886418667 / 16000000000000) = 1/(500000000000 / 21511886418667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (235109551 / 62500000) (1880876411 / 500000000) (Real.log (21511886418667 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21511886418667 / 500000000000) = -Real.log (500000000000 / 21511886418667) := by
    rw [show ((21511886418667 / 500000000000) : ℝ) = ((500000000000 / 21511886418667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (746987103 / 200000000) ≤ -Real.log (500000000000 / 20942662320953) ∧
    -Real.log (500000000000 / 20942662320953) ≤ (3734935521 / 1000000000) := by
  have h := checkLog_sound (w := (4942662320953 / 36942662320953)) (n := 12)
    (lo := (53839923 / 200000000)) (hi := (1051561 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20942662320953 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20942662320953 / 16000000000000) = 1/(500000000000 / 20942662320953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (746987103 / 200000000) (3734935521 / 1000000000) (Real.log (20942662320953 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (20942662320953 / 500000000000) = -Real.log (500000000000 / 20942662320953) := by
    rw [show ((20942662320953 / 500000000000) : ℝ) = ((500000000000 / 20942662320953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1873818003 / 500000000) ≤ -Real.log (100000000000 / 4242068127049) ∧
    -Real.log (100000000000 / 4242068127049) ≤ (936909003 / 250000000) := by
  have h := checkLog_sound (w := (1042068127049 / 7442068127049)) (n := 12)
    (lo := (140950053 / 500000000)) (hi := (281900107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4242068127049 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4242068127049 / 3200000000000) = 1/(100000000000 / 4242068127049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1873818003 / 500000000) (936909003 / 250000000) (Real.log (4242068127049 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4242068127049 / 100000000000) = -Real.log (100000000000 / 4242068127049) := by
    rw [show ((4242068127049 / 100000000000) : ℝ) = ((100000000000 / 4242068127049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0124

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0125Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0125
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

theorem reflection_log_1_neg : (166044219 / 250000000) ≤ -Real.log (12800 / 24869) ∧
    -Real.log (12800 / 24869) ≤ (664176877 / 1000000000) := by
  have h := checkLog_sound (w := (12069 / 37669)) (n := 12)
    (lo := (166044219 / 250000000)) (hi := (664176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24869 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24869 / 12800) = 1/(12800 / 24869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166044219 / 250000000) (664176877 / 1000000000) (Real.log (24869 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24869 / 12800) = -Real.log (12800 / 24869) := by
    rw [show ((24869 / 12800) : ℝ) = ((12800 / 24869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2862786987 / 1000000000) ≤ -Real.log (731 / 12800) ∧
    -Real.log (731 / 12800) ≤ (178924187 / 62500000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 731) = 1/(731 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-178924187 / 62500000) (-2862786987 / 1000000000) (Real.log (731 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331897401 / 500000000) ≤ -Real.log (25600 / 49719) ∧
    -Real.log (25600 / 49719) ≤ (663794803 / 1000000000) := by
  have h := checkLog_sound (w := (24119 / 75319)) (n := 12)
    (lo := (331897401 / 500000000)) (hi := (663794803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49719 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49719 / 25600) = 1/(25600 / 49719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331897401 / 500000000) (663794803 / 1000000000) (Real.log (49719 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49719 / 25600) = -Real.log (25600 / 49719) := by
    rw [show ((49719 / 25600) : ℝ) = ((25600 / 49719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2849874813 / 1000000000) ≤ -Real.log (1481 / 25600) ∧
    -Real.log (1481 / 25600) ≤ (1424937409 / 500000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1481) = 1/(1481 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1424937409 / 500000000) (-2849874813 / 1000000000) (Real.log (1481 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (634342191 / 1000000000) ≤ -Real.log (6400 / 12069) ∧
    -Real.log (6400 / 12069) ≤ (39646387 / 62500000) := by
  have h := checkLog_sound (w := (5669 / 18469)) (n := 12)
    (lo := (634342191 / 1000000000)) (hi := (39646387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12069 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12069 / 6400) = 1/(6400 / 12069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (634342191 / 1000000000) (39646387 / 62500000) (Real.log (12069 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12069 / 6400) = -Real.log (6400 / 12069) := by
    rw [show ((12069 / 6400) : ℝ) = ((6400 / 12069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2169639807 / 1000000000) ≤ -Real.log (731 / 6400) ∧
    -Real.log (731 / 6400) ≤ (2169639811 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 731) = 1/(731 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2169639811 / 1000000000) (-2169639807 / 1000000000) (Real.log (731 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (31677737 / 50000000) ≤ -Real.log (12800 / 24119) ∧
    -Real.log (12800 / 24119) ≤ (633554741 / 1000000000) := by
  have h := checkLog_sound (w := (11319 / 36919)) (n := 12)
    (lo := (31677737 / 50000000)) (hi := (633554741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24119 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24119 / 12800) = 1/(12800 / 24119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (31677737 / 50000000) (633554741 / 1000000000) (Real.log (24119 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24119 / 12800) = -Real.log (12800 / 24119) := by
    rw [show ((24119 / 12800) : ℝ) = ((12800 / 24119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2156727633 / 1000000000) ≤ -Real.log (1481 / 12800) ∧
    -Real.log (1481 / 12800) ≤ (2156727637 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1481) = 1/(1481 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2156727637 / 1000000000) (-2156727633 / 1000000000) (Real.log (1481 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669601647 / 1000000000) ≤ -Real.log (1000000 / 1953459) ∧
    -Real.log (1000000 / 1953459) ≤ (41850103 / 62500000) := by
  have h := checkLog_sound (w := (953459 / 2953459)) (n := 12)
    (lo := (669601647 / 1000000000)) (hi := (41850103 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953459 / 1000000) = 1/(1000000 / 1953459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669601647 / 1000000000) (41850103 / 62500000) (Real.log (1953459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1953459 / 1000000) = -Real.log (1000000 / 1953459) := by
    rw [show ((1953459 / 1000000) : ℝ) = ((1000000 / 1953459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (47928463 / 15625000) ≤ -Real.log (46541 / 1000000) ∧
    -Real.log (46541 / 1000000) ≤ (3067421637 / 1000000000) := by
  have h := checkLog_sound (w := (15959 / 109041)) (n := 12)
    (lo := (18427057 / 62500000)) (hi := (294832913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 46541) = 1/(46541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3067421637 / 1000000000) (-47928463 / 15625000) (Real.log (46541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334942859 / 500000000) ≤ -Real.log (500000 / 977007) ∧
    -Real.log (500000 / 977007) ≤ (669885719 / 1000000000) := by
  have h := checkLog_sound (w := (477007 / 1477007)) (n := 12)
    (lo := (334942859 / 500000000)) (hi := (669885719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977007 / 500000) = 1/(500000 / 977007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334942859 / 500000000) (669885719 / 1000000000) (Real.log (977007 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (977007 / 500000) = -Real.log (500000 / 977007) := by
    rw [show ((977007 / 500000) : ℝ) = ((500000 / 977007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1539709137 / 500000000) ≤ -Real.log (22993 / 500000) ∧
    -Real.log (22993 / 500000) ≤ (3079418279 / 1000000000) := by
  have h := checkLog_sound (w := (8257 / 54243)) (n := 12)
    (lo := (153414777 / 500000000)) (hi := (61365911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22993) = 1/(22993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3079418279 / 1000000000) (-1539709137 / 500000000) (Real.log (22993 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (669259119 / 1000000000) ≤ -Real.log (100000 / 195279) ∧
    -Real.log (100000 / 195279) ≤ (8365739 / 12500000) := by
  have h := checkLog_sound (w := (95279 / 295279)) (n := 12)
    (lo := (669259119 / 1000000000)) (hi := (8365739 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195279 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195279 / 100000) = 1/(100000 / 195279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (669259119 / 1000000000) (8365739 / 12500000) (Real.log (195279 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (195279 / 100000) = -Real.log (100000 / 195279) := by
    rw [show ((195279 / 100000) : ℝ) = ((100000 / 195279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1526574771 / 500000000) ≤ -Real.log (4721 / 100000) ∧
    -Real.log (4721 / 100000) ≤ (3053149547 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 10971)) (n := 12)
    (lo := (140280411 / 500000000)) (hi := (280560823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4721) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4721) = 1/(4721 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3053149547 / 1000000000) (-1526574771 / 500000000) (Real.log (4721 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334776763 / 500000000) ≤ -Real.log (200000 / 390673) ∧
    -Real.log (200000 / 390673) ≤ (669553527 / 1000000000) := by
  have h := checkLog_sound (w := (190673 / 590673)) (n := 12)
    (lo := (334776763 / 500000000)) (hi := (669553527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390673 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390673 / 200000) = 1/(200000 / 390673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334776763 / 500000000) (669553527 / 1000000000) (Real.log (390673 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390673 / 200000) = -Real.log (200000 / 390673) := by
    rw [show ((390673 / 200000) : ℝ) = ((200000 / 390673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (383175493 / 125000000) ≤ -Real.log (9327 / 200000) ∧
    -Real.log (9327 / 200000) ≤ (3065403949 / 1000000000) := by
  have h := checkLog_sound (w := (3173 / 21827)) (n := 12)
    (lo := (36601903 / 125000000)) (hi := (11712609 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9327) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 9327) = 1/(9327 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3065403949 / 1000000000) (-383175493 / 125000000) (Real.log (9327 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1868511639 / 500000000) ≤ -Real.log (250000000000 / 10493215659311) ∧
    -Real.log (250000000000 / 10493215659311) ≤ (934255821 / 250000000) := by
  have h := checkLog_sound (w := (2493215659311 / 18493215659311)) (n := 12)
    (lo := (135643689 / 500000000)) (hi := (271287379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10493215659311 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10493215659311 / 8000000000000) = 1/(250000000000 / 10493215659311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1868511639 / 500000000) (934255821 / 250000000) (Real.log (10493215659311 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10493215659311 / 250000000000) = -Real.log (250000000000 / 10493215659311) := by
    rw [show ((10493215659311 / 250000000000) : ℝ) = ((250000000000 / 10493215659311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (468662999 / 125000000) ≤ -Real.log (31250000000 / 1327859294133) ∧
    -Real.log (31250000000 / 1327859294133) ≤ (1874651999 / 500000000) := by
  have h := checkLog_sound (w := (327859294133 / 2327859294133)) (n := 12)
    (lo := (70892023 / 250000000)) (hi := (283568093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327859294133 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1327859294133 / 1000000000000) = 1/(31250000000 / 1327859294133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (468662999 / 125000000) (1874651999 / 500000000) (Real.log (1327859294133 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1327859294133 / 31250000000) = -Real.log (31250000000 / 1327859294133) := by
    rw [show ((1327859294133 / 31250000000) : ℝ) = ((31250000000 / 1327859294133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (186120433 / 50000000) ≤ -Real.log (7812500000 / 323155515251) ∧
    -Real.log (7812500000 / 323155515251) ≤ (1861204333 / 500000000) := by
  have h := checkLog_sound (w := (73155515251 / 573155515251)) (n := 12)
    (lo := (6416819 / 25000000)) (hi := (256672761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323155515251 / 250000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(323155515251 / 250000000000) = 1/(7812500000 / 323155515251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (186120433 / 50000000) (1861204333 / 500000000) (Real.log (323155515251 / 7812500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (323155515251 / 7812500000) = -Real.log (7812500000 / 323155515251) := by
    rw [show ((323155515251 / 7812500000) : ℝ) = ((7812500000 / 323155515251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (373495747 / 100000000) ≤ -Real.log (500000000000 / 20943122118581) ∧
    -Real.log (500000000000 / 20943122118581) ≤ (933739369 / 250000000) := by
  have h := checkLog_sound (w := (4943122118581 / 36943122118581)) (n := 12)
    (lo := (26922157 / 100000000)) (hi := (269221571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20943122118581 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20943122118581 / 16000000000000) = 1/(500000000000 / 20943122118581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (373495747 / 100000000) (933739369 / 250000000) (Real.log (20943122118581 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20943122118581 / 500000000000) = -Real.log (500000000000 / 20943122118581) := by
    rw [show ((20943122118581 / 500000000000) : ℝ) = ((500000000000 / 20943122118581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0125

end


