-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0040Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0040Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:58.545985+00:00
-- url     : https://prove2.me/theorems/eeef3d8d-8816-4a72-9b39-5a6b8c2c871e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0044Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0044Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0044Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0040Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0041Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0042Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0043Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0044Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040
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

theorem reflection_log_1_neg : (135999921 / 200000000) ≤ -Real.log (4096 / 8085) ∧
    -Real.log (4096 / 8085) ≤ (339999803 / 500000000) := by
  have h := checkLog_sound (w := (3989 / 12181)) (n := 12)
    (lo := (135999921 / 200000000)) (hi := (339999803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8085 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8085 / 4096) = 1/(4096 / 8085) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135999921 / 200000000) (339999803 / 500000000) (Real.log (8085 / 4096)) := by
  have h := reflection_log_1_neg
  have he : Real.log (8085 / 4096) = -Real.log (4096 / 8085) := by
    rw [show ((8085 / 4096) : ℝ) = ((4096 / 8085) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3644937329 / 1000000000) ≤ -Real.log (107 / 4096) ∧
    -Real.log (107 / 4096) ≤ (728987467 / 200000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(128 / 107) = 1/(107 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) (Real.log (107 / 4096)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679905599 / 1000000000) ≤ -Real.log (51200 / 101053) ∧
    -Real.log (51200 / 101053) ≤ (424941 / 625000) := by
  have h := checkLog_sound (w := (49853 / 152253)) (n := 12)
    (lo := (679905599 / 1000000000)) (hi := (424941 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101053 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101053 / 51200) = 1/(51200 / 101053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679905599 / 1000000000) (424941 / 625000) (Real.log (101053 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101053 / 51200) = -Real.log (51200 / 101053) := by
    rw [show ((101053 / 51200) : ℝ) = ((51200 / 101053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3637859631 / 1000000000) ≤ -Real.log (1347 / 51200) ∧
    -Real.log (1347 / 51200) ≤ (3637859637 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1347) = 1/(1347 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) (Real.log (1347 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (133335373 / 200000000) ≤ -Real.log (2048 / 3989) ∧
    -Real.log (2048 / 3989) ≤ (333338433 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 6037)) (n := 12)
    (lo := (133335373 / 200000000)) (hi := (333338433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2048) = 1/(2048 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (133335373 / 200000000) (333338433 / 500000000) (Real.log (3989 / 2048)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3989 / 2048) = -Real.log (2048 / 3989) := by
    rw [show ((3989 / 2048) : ℝ) = ((2048 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2951790149 / 1000000000) ≤ -Real.log (107 / 2048) ∧
    -Real.log (107 / 2048) ≤ (1475895077 / 500000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(128 / 107) = 1/(107 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) (Real.log (107 / 2048)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (666486323 / 1000000000) ≤ -Real.log (25600 / 49853) ∧
    -Real.log (25600 / 49853) ≤ (166621581 / 250000000) := by
  have h := checkLog_sound (w := (24253 / 75453)) (n := 12)
    (lo := (666486323 / 1000000000)) (hi := (166621581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49853 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49853 / 25600) = 1/(25600 / 49853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (666486323 / 1000000000) (166621581 / 250000000) (Real.log (49853 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49853 / 25600) = -Real.log (25600 / 49853) := by
    rw [show ((49853 / 25600) : ℝ) = ((25600 / 49853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2944712451 / 1000000000) ≤ -Real.log (1347 / 25600) ∧
    -Real.log (1347 / 25600) ≤ (368089057 / 125000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1347) = 1/(1347 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) (Real.log (1347 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85252753 / 125000000) ≤ -Real.log (1000000 / 1977873) ∧
    -Real.log (1000000 / 1977873) ≤ (27280881 / 40000000) := by
  have h := checkLog_sound (w := (977873 / 2977873)) (n := 12)
    (lo := (85252753 / 125000000)) (hi := (27280881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977873 / 1000000) = 1/(1000000 / 1977873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85252753 / 125000000) (27280881 / 40000000) (Real.log (1977873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977873 / 1000000) = -Real.log (1000000 / 1977873) := by
    rw [show ((1977873 / 1000000) : ℝ) = ((1000000 / 1977873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3810956693 / 1000000000) ≤ -Real.log (22127 / 1000000) ∧
    -Real.log (22127 / 1000000) ≤ (3810956699 / 1000000000) := by
  have h := checkLog_sound (w := (9123 / 53377)) (n := 12)
    (lo := (345220793 / 1000000000)) (hi := (172610397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22127) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22127) = 1/(22127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3810956699 / 1000000000) (-3810956693 / 1000000000) (Real.log (22127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682097861 / 1000000000) ≤ -Real.log (1000000 / 1978023) ∧
    -Real.log (1000000 / 1978023) ≤ (341048931 / 500000000) := by
  have h := checkLog_sound (w := (978023 / 2978023)) (n := 12)
    (lo := (682097861 / 1000000000)) (hi := (341048931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978023 / 1000000) = 1/(1000000 / 1978023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682097861 / 1000000000) (341048931 / 500000000) (Real.log (1978023 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978023 / 1000000) = -Real.log (1000000 / 1978023) := by
    rw [show ((1978023 / 1000000) : ℝ) = ((1000000 / 1978023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (477219853 / 125000000) ≤ -Real.log (21977 / 1000000) ∧
    -Real.log (21977 / 1000000) ≤ (381775883 / 100000000) := by
  have h := checkLog_sound (w := (9273 / 53227)) (n := 12)
    (lo := (88005731 / 250000000)) (hi := (14080917 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21977) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21977) = 1/(21977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-381775883 / 100000000) (-477219853 / 125000000) (Real.log (21977 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136392877 / 200000000) ≤ -Real.log (1000000 / 1977759) ∧
    -Real.log (1000000 / 1977759) ≤ (340982193 / 500000000) := by
  have h := checkLog_sound (w := (977759 / 2977759)) (n := 12)
    (lo := (136392877 / 200000000)) (hi := (340982193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977759 / 1000000) = 1/(1000000 / 1977759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136392877 / 200000000) (340982193 / 500000000) (Real.log (1977759 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1977759 / 1000000) = -Real.log (1000000 / 1977759) := by
    rw [show ((1977759 / 1000000) : ℝ) = ((1000000 / 1977759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3805817843 / 1000000000) ≤ -Real.log (22241 / 1000000) ∧
    -Real.log (22241 / 1000000) ≤ (3805817849 / 1000000000) := by
  have h := checkLog_sound (w := (9009 / 53491)) (n := 12)
    (lo := (340081943 / 1000000000)) (hi := (42510243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22241) = 1/(22241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3805817849 / 1000000000) (-3805817843 / 1000000000) (Real.log (22241 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682041237 / 1000000000) ≤ -Real.log (1000000 / 1977911) ∧
    -Real.log (1000000 / 1977911) ≤ (341020619 / 500000000) := by
  have h := checkLog_sound (w := (977911 / 2977911)) (n := 12)
    (lo := (682041237 / 1000000000)) (hi := (341020619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977911 / 1000000) = 1/(1000000 / 1977911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682041237 / 1000000000) (341020619 / 500000000) (Real.log (1977911 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977911 / 1000000) = -Real.log (1000000 / 1977911) := by
    rw [show ((1977911 / 1000000) : ℝ) = ((1000000 / 1977911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3812675529 / 1000000000) ≤ -Real.log (22089 / 1000000) ∧
    -Real.log (22089 / 1000000) ≤ (762535107 / 200000000) := by
  have h := checkLog_sound (w := (9161 / 53339)) (n := 12)
    (lo := (346939629 / 1000000000)) (hi := (34693963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22089) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22089) = 1/(22089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-762535107 / 200000000) (-3812675529 / 1000000000) (Real.log (22089 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2246489359 / 500000000) ≤ -Real.log (31250000000 / 2793353425679) ∧
    -Real.log (31250000000 / 2793353425679) ≤ (179719149 / 40000000) := by
  have h := checkLog_sound (w := (793353425679 / 4793353425679)) (n := 12)
    (lo := (167047819 / 500000000)) (hi := (334095639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2793353425679 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2793353425679 / 2000000000000) = 1/(31250000000 / 2793353425679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2246489359 / 500000000) (179719149 / 40000000) (Real.log (2793353425679 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2793353425679 / 31250000000) = -Real.log (31250000000 / 2793353425679) := by
    rw [show ((2793353425679 / 31250000000) : ℝ) = ((31250000000 / 2793353425679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1124964171 / 250000000) ≤ -Real.log (500000000000 / 45002115848387) ∧
    -Real.log (500000000000 / 45002115848387) ≤ (4499856691 / 1000000000) := by
  have h := checkLog_sound (w := (13002115848387 / 77002115848387)) (n := 12)
    (lo := (85243401 / 250000000)) (hi := (68194721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45002115848387 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45002115848387 / 32000000000000) = 1/(500000000000 / 45002115848387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1124964171 / 250000000) (4499856691 / 1000000000) (Real.log (45002115848387 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45002115848387 / 500000000000) = -Real.log (500000000000 / 45002115848387) := by
    rw [show ((45002115848387 / 500000000000) : ℝ) = ((500000000000 / 45002115848387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1121945557 / 250000000) ≤ -Real.log (500000000000 / 44462007103997) ∧
    -Real.log (500000000000 / 44462007103997) ≤ (897556447 / 200000000) := by
  have h := checkLog_sound (w := (12462007103997 / 76462007103997)) (n := 12)
    (lo := (82224787 / 250000000)) (hi := (328899149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44462007103997 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44462007103997 / 32000000000000) = 1/(500000000000 / 44462007103997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1121945557 / 250000000) (897556447 / 200000000) (Real.log (44462007103997 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44462007103997 / 500000000000) = -Real.log (500000000000 / 44462007103997) := by
    rw [show ((44462007103997 / 500000000000) : ℝ) = ((500000000000 / 44462007103997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (898943353 / 200000000) ≤ -Real.log (250000000000 / 22385701027661) ∧
    -Real.log (250000000000 / 22385701027661) ≤ (1123679193 / 250000000) := by
  have h := checkLog_sound (w := (6385701027661 / 38385701027661)) (n := 12)
    (lo := (67166737 / 200000000)) (hi := (167916843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22385701027661 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22385701027661 / 16000000000000) = 1/(250000000000 / 22385701027661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (898943353 / 200000000) (1123679193 / 250000000) (Real.log (22385701027661 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22385701027661 / 250000000000) = -Real.log (250000000000 / 22385701027661) := by
    rw [show ((22385701027661 / 250000000000) : ℝ) = ((250000000000 / 22385701027661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041
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

theorem reflection_log_1_neg : (679905599 / 1000000000) ≤ -Real.log (51200 / 101053) ∧
    -Real.log (51200 / 101053) ≤ (424941 / 625000) := by
  have h := checkLog_sound (w := (49853 / 152253)) (n := 12)
    (lo := (679905599 / 1000000000)) (hi := (424941 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101053 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101053 / 51200) = 1/(51200 / 101053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (679905599 / 1000000000) (424941 / 625000) (Real.log (101053 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101053 / 51200) = -Real.log (51200 / 101053) := by
    rw [show ((101053 / 51200) : ℝ) = ((51200 / 101053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3637859631 / 1000000000) ≤ -Real.log (1347 / 51200) ∧
    -Real.log (1347 / 51200) ≤ (3637859637 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1347) = 1/(1347 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) (Real.log (1347 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135962317 / 200000000) ≤ -Real.log (102400 / 202087) ∧
    -Real.log (102400 / 202087) ≤ (339905793 / 500000000) := by
  have h := checkLog_sound (w := (99687 / 304487)) (n := 12)
    (lo := (135962317 / 200000000)) (hi := (339905793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202087 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202087 / 102400) = 1/(102400 / 202087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (135962317 / 200000000) (339905793 / 500000000) (Real.log (202087 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202087 / 102400) = -Real.log (102400 / 202087) := by
    rw [show ((202087 / 102400) : ℝ) = ((102400 / 202087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (907707919 / 250000000) ≤ -Real.log (2713 / 102400) ∧
    -Real.log (2713 / 102400) ≤ (1815415841 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2713) = 1/(2713 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) (Real.log (2713 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (666486323 / 1000000000) ≤ -Real.log (25600 / 49853) ∧
    -Real.log (25600 / 49853) ≤ (166621581 / 250000000) := by
  have h := checkLog_sound (w := (24253 / 75453)) (n := 12)
    (lo := (666486323 / 1000000000)) (hi := (166621581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49853 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49853 / 25600) = 1/(25600 / 49853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (666486323 / 1000000000) (166621581 / 250000000) (Real.log (49853 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49853 / 25600) = -Real.log (25600 / 49853) := by
    rw [show ((49853 / 25600) : ℝ) = ((25600 / 49853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2944712451 / 1000000000) ≤ -Real.log (1347 / 25600) ∧
    -Real.log (1347 / 25600) ≤ (368089057 / 125000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1347) = 1/(1347 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) (Real.log (1347 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (133259149 / 200000000) ≤ -Real.log (51200 / 99687) ∧
    -Real.log (51200 / 99687) ≤ (333147873 / 500000000) := by
  have h := checkLog_sound (w := (48487 / 150887)) (n := 12)
    (lo := (133259149 / 200000000)) (hi := (333147873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99687 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99687 / 51200) = 1/(51200 / 99687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (133259149 / 200000000) (333147873 / 500000000) (Real.log (99687 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99687 / 51200) = -Real.log (51200 / 99687) := by
    rw [show ((99687 / 51200) : ℝ) = ((51200 / 99687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (183605281 / 62500000) ≤ -Real.log (2713 / 51200) ∧
    -Real.log (2713 / 51200) ≤ (2937684501 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2713) = 1/(2713 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) (Real.log (2713 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340973091 / 500000000) ≤ -Real.log (1000000 / 1977723) ∧
    -Real.log (1000000 / 1977723) ≤ (681946183 / 1000000000) := by
  have h := checkLog_sound (w := (977723 / 2977723)) (n := 12)
    (lo := (340973091 / 500000000)) (hi := (681946183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977723 / 1000000) = 1/(1000000 / 1977723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340973091 / 500000000) (681946183 / 1000000000) (Real.log (1977723 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977723 / 1000000) = -Real.log (1000000 / 1977723) := by
    rw [show ((1977723 / 1000000) : ℝ) = ((1000000 / 1977723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95105013 / 25000000) ≤ -Real.log (22277 / 1000000) ∧
    -Real.log (22277 / 1000000) ≤ (1902100263 / 500000000) := by
  have h := checkLog_sound (w := (8973 / 53527)) (n := 12)
    (lo := (16923231 / 50000000)) (hi := (338464621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22277) = 1/(22277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1902100263 / 500000000) (-95105013 / 25000000) (Real.log (22277 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68202253 / 100000000) ≤ -Real.log (500000 / 988937) ∧
    -Real.log (500000 / 988937) ≤ (682022531 / 1000000000) := by
  have h := checkLog_sound (w := (488937 / 1488937)) (n := 12)
    (lo := (68202253 / 100000000)) (hi := (682022531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988937 / 500000) = 1/(500000 / 988937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68202253 / 100000000) (682022531 / 1000000000) (Real.log (988937 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988937 / 500000) = -Real.log (500000 / 988937) := by
    rw [show ((988937 / 500000) : ℝ) = ((500000 / 988937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (119093809 / 31250000) ≤ -Real.log (11063 / 500000) ∧
    -Real.log (11063 / 500000) ≤ (1905500947 / 500000000) := by
  have h := checkLog_sound (w := (2281 / 13344)) (n := 12)
    (lo := (86316497 / 250000000)) (hi := (345265989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11063) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11063) = 1/(11063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1905500947 / 500000000) (-119093809 / 31250000) (Real.log (11063 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681888033 / 1000000000) ≤ -Real.log (125000 / 247201) ∧
    -Real.log (125000 / 247201) ≤ (340944017 / 500000000) := by
  have h := checkLog_sound (w := (122201 / 372201)) (n := 12)
    (lo := (681888033 / 1000000000)) (hi := (340944017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247201 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247201 / 125000) = 1/(125000 / 247201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681888033 / 1000000000) (340944017 / 500000000) (Real.log (247201 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247201 / 125000) = -Real.log (125000 / 247201) := by
    rw [show ((247201 / 125000) : ℝ) = ((125000 / 247201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3799051523 / 1000000000) ≤ -Real.log (2799 / 125000) ∧
    -Real.log (2799 / 125000) ≤ (3799051529 / 1000000000) := by
  have h := checkLog_sound (w := (4429 / 26821)) (n := 12)
    (lo := (333315623 / 1000000000)) (hi := (41664453 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11196) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11196) = 1/(2799 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3799051529 / 1000000000) (-3799051523 / 1000000000) (Real.log (2799 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681964891 / 1000000000) ≤ -Real.log (6250 / 12361) ∧
    -Real.log (6250 / 12361) ≤ (170491223 / 250000000) := by
  have h := checkLog_sound (w := (6111 / 18611)) (n := 12)
    (lo := (681964891 / 1000000000)) (hi := (170491223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12361 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12361 / 6250) = 1/(6250 / 12361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681964891 / 1000000000) (170491223 / 250000000) (Real.log (12361 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (12361 / 6250) = -Real.log (6250 / 12361) := by
    rw [show ((12361 / 6250) : ℝ) = ((6250 / 12361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1902931403 / 500000000) ≤ -Real.log (139 / 6250) ∧
    -Real.log (139 / 6250) ≤ (951465703 / 250000000) := by
  have h := checkLog_sound (w := (901 / 5349)) (n := 12)
    (lo := (170063453 / 500000000)) (hi := (340126907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2224) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2224) = 1/(139 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-951465703 / 250000000) (-1902931403 / 500000000) (Real.log (139 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2243073351 / 500000000) ≤ -Real.log (500000000000 / 44389347757777) ∧
    -Real.log (500000000000 / 44389347757777) ≤ (4486146709 / 1000000000) := by
  have h := checkLog_sound (w := (12389347757777 / 76389347757777)) (n := 12)
    (lo := (163631811 / 500000000)) (hi := (327263623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44389347757777 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44389347757777 / 32000000000000) = 1/(500000000000 / 44389347757777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2243073351 / 500000000) (4486146709 / 1000000000) (Real.log (44389347757777 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44389347757777 / 500000000000) = -Real.log (500000000000 / 44389347757777) := by
    rw [show ((44389347757777 / 500000000000) : ℝ) = ((500000000000 / 44389347757777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2246512209 / 500000000) ≤ -Real.log (500000000000 / 44695697369611) ∧
    -Real.log (500000000000 / 44695697369611) ≤ (179720977 / 40000000) := by
  have h := checkLog_sound (w := (12695697369611 / 76695697369611)) (n := 12)
    (lo := (167070669 / 500000000)) (hi := (334141339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44695697369611 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44695697369611 / 32000000000000) = 1/(500000000000 / 44695697369611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2246512209 / 500000000) (179720977 / 40000000) (Real.log (44695697369611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44695697369611 / 500000000000) = -Real.log (500000000000 / 44695697369611) := by
    rw [show ((44695697369611 / 500000000000) : ℝ) = ((500000000000 / 44695697369611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1120234889 / 250000000) ≤ -Real.log (125000000000 / 11039701679171) ∧
    -Real.log (125000000000 / 11039701679171) ≤ (4480939563 / 1000000000) := by
  have h := checkLog_sound (w := (3039701679171 / 19039701679171)) (n := 12)
    (lo := (80514119 / 250000000)) (hi := (322056477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11039701679171 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11039701679171 / 8000000000000) = 1/(125000000000 / 11039701679171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1120234889 / 250000000) (4480939563 / 1000000000) (Real.log (11039701679171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11039701679171 / 125000000000) = -Real.log (125000000000 / 11039701679171) := by
    rw [show ((11039701679171 / 125000000000) : ℝ) = ((125000000000 / 11039701679171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4487827697 / 1000000000) ≤ -Real.log (500000000000 / 44464028776979) ∧
    -Real.log (500000000000 / 44464028776979) ≤ (560978463 / 125000000) := by
  have h := checkLog_sound (w := (12464028776979 / 76464028776979)) (n := 12)
    (lo := (328944617 / 1000000000)) (hi := (164472309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44464028776979 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44464028776979 / 32000000000000) = 1/(500000000000 / 44464028776979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4487827697 / 1000000000) (560978463 / 125000000) (Real.log (44464028776979 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (44464028776979 / 500000000000) = -Real.log (500000000000 / 44464028776979) := by
    rw [show ((44464028776979 / 500000000000) : ℝ) = ((500000000000 / 44464028776979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042
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

theorem reflection_log_1_neg : (135962317 / 200000000) ≤ -Real.log (102400 / 202087) ∧
    -Real.log (102400 / 202087) ≤ (339905793 / 500000000) := by
  have h := checkLog_sound (w := (99687 / 304487)) (n := 12)
    (lo := (135962317 / 200000000)) (hi := (339905793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202087 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202087 / 102400) = 1/(102400 / 202087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135962317 / 200000000) (339905793 / 500000000) (Real.log (202087 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202087 / 102400) = -Real.log (102400 / 202087) := by
    rw [show ((202087 / 102400) : ℝ) = ((102400 / 202087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (907707919 / 250000000) ≤ -Real.log (2713 / 102400) ∧
    -Real.log (2713 / 102400) ≤ (1815415841 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2713) = 1/(2713 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) (Real.log (2713 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679717561 / 1000000000) ≤ -Real.log (25600 / 50517) ∧
    -Real.log (25600 / 50517) ≤ (339858781 / 500000000) := by
  have h := checkLog_sound (w := (24917 / 76117)) (n := 12)
    (lo := (679717561 / 1000000000)) (hi := (339858781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50517 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50517 / 25600) = 1/(25600 / 50517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679717561 / 1000000000) (339858781 / 500000000) (Real.log (50517 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50517 / 25600) = -Real.log (25600 / 50517) := by
    rw [show ((50517 / 25600) : ℝ) = ((25600 / 50517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113245399 / 31250000) ≤ -Real.log (683 / 25600) ∧
    -Real.log (683 / 25600) ≤ (1811926387 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 683) = 1/(683 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) (Real.log (683 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (133259149 / 200000000) ≤ -Real.log (51200 / 99687) ∧
    -Real.log (51200 / 99687) ≤ (333147873 / 500000000) := by
  have h := checkLog_sound (w := (48487 / 150887)) (n := 12)
    (lo := (133259149 / 200000000)) (hi := (333147873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99687 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99687 / 51200) = 1/(51200 / 99687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (133259149 / 200000000) (333147873 / 500000000) (Real.log (99687 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99687 / 51200) = -Real.log (51200 / 99687) := by
    rw [show ((99687 / 51200) : ℝ) = ((51200 / 99687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (183605281 / 62500000) ≤ -Real.log (2713 / 51200) ∧
    -Real.log (2713 / 51200) ≤ (2937684501 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2713) = 1/(2713 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) (Real.log (2713 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (66610513 / 100000000) ≤ -Real.log (12800 / 24917) ∧
    -Real.log (12800 / 24917) ≤ (666105131 / 1000000000) := by
  have h := checkLog_sound (w := (12117 / 37717)) (n := 12)
    (lo := (66610513 / 100000000)) (hi := (666105131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24917 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24917 / 12800) = 1/(12800 / 24917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (66610513 / 100000000) (666105131 / 1000000000) (Real.log (24917 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24917 / 12800) = -Real.log (12800 / 24917) := by
    rw [show ((24917 / 12800) : ℝ) = ((12800 / 24917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (732676397 / 250000000) ≤ -Real.log (683 / 12800) ∧
    -Real.log (683 / 12800) ≤ (2930705593 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 683) = 1/(683 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) (Real.log (683 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17046771 / 25000000) ≤ -Real.log (500000 / 988787) ∧
    -Real.log (500000 / 988787) ≤ (681870841 / 1000000000) := by
  have h := checkLog_sound (w := (488787 / 1488787)) (n := 12)
    (lo := (17046771 / 25000000)) (hi := (681870841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988787 / 500000) = 1/(500000 / 988787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17046771 / 25000000) (681870841 / 1000000000) (Real.log (988787 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (988787 / 500000) = -Real.log (500000 / 988787) := by
    rw [show ((988787 / 500000) : ℝ) = ((500000 / 988787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (949383569 / 250000000) ≤ -Real.log (11213 / 500000) ∧
    -Real.log (11213 / 500000) ≤ (1898767141 / 500000000) := by
  have h := checkLog_sound (w := (2206 / 13419)) (n := 12)
    (lo := (41474797 / 125000000)) (hi := (331798377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11213) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11213) = 1/(11213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1898767141 / 500000000) (-949383569 / 250000000) (Real.log (11213 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10655417 / 15625000) ≤ -Real.log (250000 / 494431) ∧
    -Real.log (250000 / 494431) ≤ (681946689 / 1000000000) := by
  have h := checkLog_sound (w := (244431 / 744431)) (n := 12)
    (lo := (10655417 / 15625000)) (hi := (681946689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494431 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494431 / 250000) = 1/(250000 / 494431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10655417 / 15625000) (681946689 / 1000000000) (Real.log (494431 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494431 / 250000) = -Real.log (250000 / 494431) := by
    rw [show ((494431 / 250000) : ℝ) = ((250000 / 494431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (380424541 / 100000000) ≤ -Real.log (5569 / 250000) ∧
    -Real.log (5569 / 250000) ≤ (475530677 / 125000000) := by
  have h := checkLog_sound (w := (4487 / 26763)) (n := 12)
    (lo := (33850951 / 100000000)) (hi := (338509511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11138) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11138) = 1/(5569 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-475530677 / 125000000) (-380424541 / 100000000) (Real.log (5569 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681812181 / 1000000000) ≤ -Real.log (500000 / 988729) ∧
    -Real.log (500000 / 988729) ≤ (340906091 / 500000000) := by
  have h := checkLog_sound (w := (488729 / 1488729)) (n := 12)
    (lo := (681812181 / 1000000000)) (hi := (340906091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988729 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988729 / 500000) = 1/(500000 / 988729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681812181 / 1000000000) (340906091 / 500000000) (Real.log (988729 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (988729 / 500000) = -Real.log (500000 / 988729) := by
    rw [show ((988729 / 500000) : ℝ) = ((500000 / 988729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2962793 / 781250) ≤ -Real.log (11271 / 500000) ∧
    -Real.log (11271 / 500000) ≤ (1896187523 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 13448)) (n := 12)
    (lo := (16331957 / 50000000)) (hi := (326639141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11271) = 1/(11271 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1896187523 / 500000000) (-2962793 / 781250) (Real.log (11271 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681888539 / 1000000000) ≤ -Real.log (1000000 / 1977609) ∧
    -Real.log (1000000 / 1977609) ≤ (34094427 / 50000000) := by
  have h := checkLog_sound (w := (977609 / 2977609)) (n := 12)
    (lo := (681888539 / 1000000000)) (hi := (34094427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977609 / 1000000) = 1/(1000000 / 1977609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681888539 / 1000000000) (34094427 / 50000000) (Real.log (1977609 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977609 / 1000000) = -Real.log (1000000 / 1977609) := by
    rw [show ((1977609 / 1000000) : ℝ) = ((1000000 / 1977609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3799096183 / 1000000000) ≤ -Real.log (22391 / 1000000) ∧
    -Real.log (22391 / 1000000) ≤ (3799096189 / 1000000000) := by
  have h := checkLog_sound (w := (8859 / 53641)) (n := 12)
    (lo := (333360283 / 1000000000)) (hi := (83340071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22391) = 1/(22391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3799096189 / 1000000000) (-3799096183 / 1000000000) (Real.log (22391 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1119851279 / 250000000) ≤ -Real.log (125000000000 / 11022774904129) ∧
    -Real.log (125000000000 / 11022774904129) ≤ (4479405123 / 1000000000) := by
  have h := checkLog_sound (w := (3022774904129 / 19022774904129)) (n := 12)
    (lo := (80130509 / 250000000)) (hi := (320522037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11022774904129 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11022774904129 / 8000000000000) = 1/(125000000000 / 11022774904129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1119851279 / 250000000) (4479405123 / 1000000000) (Real.log (11022774904129 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11022774904129 / 125000000000) = -Real.log (125000000000 / 11022774904129) := by
    rw [show ((11022774904129 / 125000000000) : ℝ) = ((125000000000 / 11022774904129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2243096049 / 500000000) ≤ -Real.log (250000000000 / 22195681450889) ∧
    -Real.log (250000000000 / 22195681450889) ≤ (897238421 / 200000000) := by
  have h := checkLog_sound (w := (6195681450889 / 38195681450889)) (n := 12)
    (lo := (163654509 / 500000000)) (hi := (327309019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22195681450889 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22195681450889 / 16000000000000) = 1/(250000000000 / 22195681450889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2243096049 / 500000000) (897238421 / 200000000) (Real.log (22195681450889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22195681450889 / 250000000000) = -Real.log (250000000000 / 22195681450889) := by
    rw [show ((22195681450889 / 250000000000) : ℝ) = ((250000000000 / 22195681450889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4474187221 / 1000000000) ≤ -Real.log (500000000000 / 43861636057137) ∧
    -Real.log (500000000000 / 43861636057137) ≤ (1118546807 / 250000000) := by
  have h := checkLog_sound (w := (11861636057137 / 75861636057137)) (n := 12)
    (lo := (315304141 / 1000000000)) (hi := (157652071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43861636057137 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43861636057137 / 32000000000000) = 1/(500000000000 / 43861636057137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4474187221 / 1000000000) (1118546807 / 250000000) (Real.log (43861636057137 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (43861636057137 / 500000000000) = -Real.log (500000000000 / 43861636057137) := by
    rw [show ((43861636057137 / 500000000000) : ℝ) = ((500000000000 / 43861636057137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2240492361 / 500000000) ≤ -Real.log (250000000000 / 22080400607387) ∧
    -Real.log (250000000000 / 22080400607387) ≤ (4480984729 / 1000000000) := by
  have h := checkLog_sound (w := (6080400607387 / 38080400607387)) (n := 12)
    (lo := (161050821 / 500000000)) (hi := (322101643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22080400607387 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22080400607387 / 16000000000000) = 1/(250000000000 / 22080400607387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2240492361 / 500000000) (4480984729 / 1000000000) (Real.log (22080400607387 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22080400607387 / 250000000000) = -Real.log (250000000000 / 22080400607387) := by
    rw [show ((22080400607387 / 250000000000) : ℝ) = ((250000000000 / 22080400607387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043
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

theorem reflection_log_1_neg : (679717561 / 1000000000) ≤ -Real.log (25600 / 50517) ∧
    -Real.log (25600 / 50517) ≤ (339858781 / 500000000) := by
  have h := checkLog_sound (w := (24917 / 76117)) (n := 12)
    (lo := (679717561 / 1000000000)) (hi := (339858781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50517 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50517 / 25600) = 1/(25600 / 50517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (679717561 / 1000000000) (339858781 / 500000000) (Real.log (50517 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50517 / 25600) = -Real.log (25600 / 50517) := by
    rw [show ((50517 / 25600) : ℝ) = ((25600 / 50517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113245399 / 31250000) ≤ -Real.log (683 / 25600) ∧
    -Real.log (683 / 25600) ≤ (1811926387 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 683) = 1/(683 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) (Real.log (683 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679623529 / 1000000000) ≤ -Real.log (102400 / 202049) ∧
    -Real.log (102400 / 202049) ≤ (67962353 / 100000000) := by
  have h := checkLog_sound (w := (99649 / 304449)) (n := 12)
    (lo := (679623529 / 1000000000)) (hi := (67962353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202049 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202049 / 102400) = 1/(102400 / 202049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679623529 / 1000000000) (67962353 / 100000000) (Real.log (202049 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202049 / 102400) = -Real.log (102400 / 202049) := by
    rw [show ((202049 / 102400) : ℝ) = ((102400 / 202049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3616922227 / 1000000000) ≤ -Real.log (2751 / 102400) ∧
    -Real.log (2751 / 102400) ≤ (3616922233 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2751) = 1/(2751 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3616922233 / 1000000000) (-3616922227 / 1000000000) (Real.log (2751 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (66610513 / 100000000) ≤ -Real.log (12800 / 24917) ∧
    -Real.log (12800 / 24917) ≤ (666105131 / 1000000000) := by
  have h := checkLog_sound (w := (12117 / 37717)) (n := 12)
    (lo := (66610513 / 100000000)) (hi := (666105131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24917 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24917 / 12800) = 1/(12800 / 24917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (66610513 / 100000000) (666105131 / 1000000000) (Real.log (24917 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24917 / 12800) = -Real.log (12800 / 24917) := by
    rw [show ((24917 / 12800) : ℝ) = ((12800 / 24917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (732676397 / 250000000) ≤ -Real.log (683 / 12800) ∧
    -Real.log (683 / 12800) ≤ (2930705593 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 683) = 1/(683 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) (Real.log (683 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (665914479 / 1000000000) ≤ -Real.log (51200 / 99649) ∧
    -Real.log (51200 / 99649) ≤ (8323931 / 12500000) := by
  have h := checkLog_sound (w := (48449 / 150849)) (n := 12)
    (lo := (665914479 / 1000000000)) (hi := (8323931 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99649 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99649 / 51200) = 1/(51200 / 99649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (665914479 / 1000000000) (8323931 / 12500000) (Real.log (99649 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99649 / 51200) = -Real.log (51200 / 99649) := by
    rw [show ((99649 / 51200) : ℝ) = ((51200 / 99649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2923775047 / 1000000000) ≤ -Real.log (2751 / 51200) ∧
    -Real.log (2751 / 51200) ≤ (730943763 / 250000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2751) = 1/(2751 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-730943763 / 250000000) (-2923775047 / 1000000000) (Real.log (2751 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681795493 / 1000000000) ≤ -Real.log (40000 / 79097) ∧
    -Real.log (40000 / 79097) ≤ (340897747 / 500000000) := by
  have h := checkLog_sound (w := (39097 / 119097)) (n := 12)
    (lo := (681795493 / 1000000000)) (hi := (340897747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79097 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79097 / 40000) = 1/(40000 / 79097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681795493 / 1000000000) (340897747 / 500000000) (Real.log (79097 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (79097 / 40000) = -Real.log (40000 / 79097) := by
    rw [show ((79097 / 40000) : ℝ) = ((40000 / 79097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236932011 / 62500000) ≤ -Real.log (903 / 40000) ∧
    -Real.log (903 / 40000) ≤ (1895456091 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2153)) (n := 12)
    (lo := (81294069 / 250000000)) (hi := (325176277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 903) = 1/(903 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1895456091 / 500000000) (-236932011 / 62500000) (Real.log (903 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340935673 / 500000000) ≤ -Real.log (40000 / 79103) ∧
    -Real.log (40000 / 79103) ≤ (681871347 / 1000000000) := by
  have h := checkLog_sound (w := (39103 / 119103)) (n := 12)
    (lo := (340935673 / 500000000)) (hi := (681871347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79103 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79103 / 40000) = 1/(40000 / 79103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340935673 / 500000000) (681871347 / 1000000000) (Real.log (79103 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79103 / 40000) = -Real.log (40000 / 79103) := by
    rw [show ((79103 / 40000) : ℝ) = ((40000 / 79103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (949394717 / 250000000) ≤ -Real.log (897 / 40000) ∧
    -Real.log (897 / 40000) ≤ (1898789437 / 500000000) := by
  have h := checkLog_sound (w := (353 / 2147)) (n := 12)
    (lo := (41480371 / 125000000)) (hi := (331842969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 897) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 897) = 1/(897 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1898789437 / 500000000) (-949394717 / 250000000) (Real.log (897 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681735817 / 1000000000) ≤ -Real.log (1000000 / 1977307) ∧
    -Real.log (1000000 / 1977307) ≤ (340867909 / 500000000) := by
  have h := checkLog_sound (w := (977307 / 2977307)) (n := 12)
    (lo := (681735817 / 1000000000)) (hi := (340867909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977307 / 1000000) = 1/(1000000 / 1977307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681735817 / 1000000000) (340867909 / 500000000) (Real.log (1977307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1977307 / 1000000) = -Real.log (1000000 / 1977307) := by
    rw [show ((1977307 / 1000000) : ℝ) = ((1000000 / 1977307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3785698769 / 1000000000) ≤ -Real.log (22693 / 1000000) ∧
    -Real.log (22693 / 1000000) ≤ (151427951 / 40000000) := by
  have h := checkLog_sound (w := (8557 / 53943)) (n := 12)
    (lo := (319962869 / 1000000000)) (hi := (31996287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22693) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22693) = 1/(22693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-151427951 / 40000000) (-3785698769 / 1000000000) (Real.log (22693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681812687 / 1000000000) ≤ -Real.log (1000000 / 1977459) ∧
    -Real.log (1000000 / 1977459) ≤ (42613293 / 62500000) := by
  have h := checkLog_sound (w := (977459 / 2977459)) (n := 12)
    (lo := (681812687 / 1000000000)) (hi := (42613293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977459 / 1000000) = 1/(1000000 / 1977459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681812687 / 1000000000) (42613293 / 62500000) (Real.log (1977459 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977459 / 1000000) = -Real.log (1000000 / 1977459) := by
    rw [show ((1977459 / 1000000) : ℝ) = ((1000000 / 1977459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1896209701 / 500000000) ≤ -Real.log (22541 / 1000000) ∧
    -Real.log (22541 / 1000000) ≤ (237026213 / 62500000) := by
  have h := checkLog_sound (w := (8709 / 53791)) (n := 12)
    (lo := (163341751 / 500000000)) (hi := (326683503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22541) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22541) = 1/(22541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-237026213 / 62500000) (-1896209701 / 500000000) (Real.log (22541 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4472707669 / 1000000000) ≤ -Real.log (250000000000 / 21898394241417) ∧
    -Real.log (250000000000 / 21898394241417) ≤ (1118176919 / 250000000) := by
  have h := checkLog_sound (w := (5898394241417 / 37898394241417)) (n := 12)
    (lo := (313824589 / 1000000000)) (hi := (31382459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21898394241417 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21898394241417 / 16000000000000) = 1/(250000000000 / 21898394241417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4472707669 / 1000000000) (1118176919 / 250000000) (Real.log (21898394241417 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21898394241417 / 250000000000) = -Real.log (250000000000 / 21898394241417) := by
    rw [show ((21898394241417 / 250000000000) : ℝ) = ((250000000000 / 21898394241417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2239725107 / 500000000) ≤ -Real.log (500000000000 / 44093088071349) ∧
    -Real.log (500000000000 / 44093088071349) ≤ (4479450221 / 1000000000) := by
  have h := checkLog_sound (w := (12093088071349 / 76093088071349)) (n := 12)
    (lo := (160283567 / 500000000)) (hi := (64113427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44093088071349 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44093088071349 / 32000000000000) = 1/(500000000000 / 44093088071349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2239725107 / 500000000) (4479450221 / 1000000000) (Real.log (44093088071349 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44093088071349 / 500000000000) = -Real.log (500000000000 / 44093088071349) := by
    rw [show ((44093088071349 / 500000000000) : ℝ) = ((500000000000 / 44093088071349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2233717293 / 500000000) ≤ -Real.log (125000000000 / 10891613052483) ∧
    -Real.log (125000000000 / 10891613052483) ≤ (4467434593 / 1000000000) := by
  have h := checkLog_sound (w := (2891613052483 / 18891613052483)) (n := 12)
    (lo := (154275753 / 500000000)) (hi := (308551507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10891613052483 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10891613052483 / 8000000000000) = 1/(125000000000 / 10891613052483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2233717293 / 500000000) (4467434593 / 1000000000) (Real.log (10891613052483 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10891613052483 / 125000000000) = -Real.log (125000000000 / 10891613052483) := by
    rw [show ((10891613052483 / 125000000000) : ℝ) = ((125000000000 / 10891613052483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4474232089 / 1000000000) ≤ -Real.log (250000000000 / 21931802049599) ∧
    -Real.log (250000000000 / 21931802049599) ≤ (139819753 / 31250000) := by
  have h := checkLog_sound (w := (5931802049599 / 37931802049599)) (n := 12)
    (lo := (315349009 / 1000000000)) (hi := (31534901 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21931802049599 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21931802049599 / 16000000000000) = 1/(250000000000 / 21931802049599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4474232089 / 1000000000) (139819753 / 31250000) (Real.log (21931802049599 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21931802049599 / 250000000000) = -Real.log (250000000000 / 21931802049599) := by
    rw [show ((21931802049599 / 250000000000) : ℝ) = ((250000000000 / 21931802049599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0044Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044
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

theorem reflection_log_1_neg : (679623529 / 1000000000) ≤ -Real.log (102400 / 202049) ∧
    -Real.log (102400 / 202049) ≤ (67962353 / 100000000) := by
  have h := checkLog_sound (w := (99649 / 304449)) (n := 12)
    (lo := (679623529 / 1000000000)) (hi := (67962353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202049 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202049 / 102400) = 1/(102400 / 202049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (679623529 / 1000000000) (67962353 / 100000000) (Real.log (202049 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202049 / 102400) = -Real.log (102400 / 202049) := by
    rw [show ((202049 / 102400) : ℝ) = ((102400 / 202049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3616922227 / 1000000000) ≤ -Real.log (2751 / 102400) ∧
    -Real.log (2751 / 102400) ≤ (3616922233 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2751) = 1/(2751 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3616922233 / 1000000000) (-3616922227 / 1000000000) (Real.log (2751 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42470593 / 62500000) ≤ -Real.log (10240 / 20203) ∧
    -Real.log (10240 / 20203) ≤ (679529489 / 1000000000) := by
  have h := checkLog_sound (w := (9963 / 30443)) (n := 12)
    (lo := (42470593 / 62500000)) (hi := (679529489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20203 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20203 / 10240) = 1/(10240 / 20203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42470593 / 62500000) (679529489 / 1000000000) (Real.log (20203 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20203 / 10240) = -Real.log (10240 / 20203) := by
    rw [show ((20203 / 10240) : ℝ) = ((10240 / 20203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3610039389 / 1000000000) ≤ -Real.log (277 / 10240) ∧
    -Real.log (277 / 10240) ≤ (722007879 / 200000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 277) = 1/(277 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-722007879 / 200000000) (-3610039389 / 1000000000) (Real.log (277 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (665914479 / 1000000000) ≤ -Real.log (51200 / 99649) ∧
    -Real.log (51200 / 99649) ≤ (8323931 / 12500000) := by
  have h := checkLog_sound (w := (48449 / 150849)) (n := 12)
    (lo := (665914479 / 1000000000)) (hi := (8323931 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99649 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99649 / 51200) = 1/(51200 / 99649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (665914479 / 1000000000) (8323931 / 12500000) (Real.log (99649 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99649 / 51200) = -Real.log (51200 / 99649) := by
    rw [show ((99649 / 51200) : ℝ) = ((51200 / 99649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2923775047 / 1000000000) ≤ -Real.log (2751 / 51200) ∧
    -Real.log (2751 / 51200) ≤ (730943763 / 250000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2751) = 1/(2751 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-730943763 / 250000000) (-2923775047 / 1000000000) (Real.log (2751 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41607737 / 62500000) ≤ -Real.log (5120 / 9963) ∧
    -Real.log (5120 / 9963) ≤ (665723793 / 1000000000) := by
  have h := checkLog_sound (w := (4843 / 15083)) (n := 12)
    (lo := (41607737 / 62500000)) (hi := (665723793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5120) = 1/(5120 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41607737 / 62500000) (665723793 / 1000000000) (Real.log (9963 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9963 / 5120) = -Real.log (5120 / 9963) := by
    rw [show ((9963 / 5120) : ℝ) = ((5120 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2916892209 / 1000000000) ≤ -Real.log (277 / 5120) ∧
    -Real.log (277 / 5120) ≤ (1458446107 / 500000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 277) = 1/(277 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1458446107 / 500000000) (-2916892209 / 1000000000) (Real.log (277 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136344129 / 200000000) ≤ -Real.log (1000000 / 1977277) ∧
    -Real.log (1000000 / 1977277) ≤ (340860323 / 500000000) := by
  have h := checkLog_sound (w := (977277 / 2977277)) (n := 12)
    (lo := (136344129 / 200000000)) (hi := (340860323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977277 / 1000000) = 1/(1000000 / 1977277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136344129 / 200000000) (340860323 / 500000000) (Real.log (1977277 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977277 / 1000000) = -Real.log (1000000 / 1977277) := by
    rw [show ((1977277 / 1000000) : ℝ) = ((1000000 / 1977277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236523603 / 62500000) ≤ -Real.log (22723 / 1000000) ∧
    -Real.log (22723 / 1000000) ≤ (1892188827 / 500000000) := by
  have h := checkLog_sound (w := (8527 / 53973)) (n := 12)
    (lo := (79660437 / 250000000)) (hi := (318641749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22723) = 1/(22723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1892188827 / 500000000) (-236523603 / 62500000) (Real.log (22723 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340897999 / 500000000) ≤ -Real.log (500000 / 988713) ∧
    -Real.log (500000 / 988713) ≤ (681795999 / 1000000000) := by
  have h := checkLog_sound (w := (488713 / 1488713)) (n := 12)
    (lo := (340897999 / 500000000)) (hi := (681795999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988713 / 500000) = 1/(500000 / 988713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340897999 / 500000000) (681795999 / 1000000000) (Real.log (988713 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988713 / 500000) = -Real.log (500000 / 988713) := by
    rw [show ((988713 / 500000) : ℝ) = ((500000 / 988713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1895478237 / 500000000) ≤ -Real.log (11287 / 500000) ∧
    -Real.log (11287 / 500000) ≤ (11846739 / 3125000) := by
  have h := checkLog_sound (w := (2169 / 13456)) (n := 12)
    (lo := (162610287 / 500000000)) (hi := (13008823 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11287) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11287) = 1/(11287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11846739 / 3125000) (-1895478237 / 500000000) (Real.log (11287 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85207431 / 125000000) ≤ -Real.log (250000 / 494289) ∧
    -Real.log (250000 / 494289) ≤ (681659449 / 1000000000) := by
  have h := checkLog_sound (w := (244289 / 744289)) (n := 12)
    (lo := (85207431 / 125000000)) (hi := (681659449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494289 / 250000) = 1/(250000 / 494289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85207431 / 125000000) (681659449 / 1000000000) (Real.log (494289 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (494289 / 250000) = -Real.log (250000 / 494289) := by
    rw [show ((494289 / 250000) : ℝ) = ((250000 / 494289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151162671 / 40000000) ≤ -Real.log (5711 / 250000) ∧
    -Real.log (5711 / 250000) ≤ (3779066781 / 1000000000) := by
  have h := checkLog_sound (w := (4203 / 27047)) (n := 12)
    (lo := (2506647 / 8000000)) (hi := (78332719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11422) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11422) = 1/(5711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3779066781 / 1000000000) (-151162671 / 40000000) (Real.log (5711 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681736323 / 1000000000) ≤ -Real.log (250000 / 494327) ∧
    -Real.log (250000 / 494327) ≤ (170434081 / 250000000) := by
  have h := checkLog_sound (w := (244327 / 744327)) (n := 12)
    (lo := (681736323 / 1000000000)) (hi := (170434081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494327 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494327 / 250000) = 1/(250000 / 494327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681736323 / 1000000000) (170434081 / 250000000) (Real.log (494327 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494327 / 250000) = -Real.log (250000 / 494327) := by
    rw [show ((494327 / 250000) : ℝ) = ((250000 / 494327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (946435709 / 250000000) ≤ -Real.log (5673 / 250000) ∧
    -Real.log (5673 / 250000) ≤ (1892871421 / 500000000) := by
  have h := checkLog_sound (w := (4279 / 26971)) (n := 12)
    (lo := (40000867 / 125000000)) (hi := (320006937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11346) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11346) = 1/(5673 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1892871421 / 500000000) (-946435709 / 250000000) (Real.log (5673 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4466098293 / 1000000000) ≤ -Real.log (125000000000 / 10877068388857) ∧
    -Real.log (125000000000 / 10877068388857) ≤ (44660983 / 10000000) := by
  have h := checkLog_sound (w := (2877068388857 / 18877068388857)) (n := 12)
    (lo := (307215213 / 1000000000)) (hi := (153607607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10877068388857 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10877068388857 / 8000000000000) = 1/(125000000000 / 10877068388857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4466098293 / 1000000000) (44660983 / 10000000) (Real.log (10877068388857 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10877068388857 / 125000000000) = -Real.log (125000000000 / 10877068388857) := by
    rw [show ((10877068388857 / 125000000000) : ℝ) = ((125000000000 / 10877068388857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4472752473 / 1000000000) ≤ -Real.log (500000000000 / 43798750775229) ∧
    -Real.log (500000000000 / 43798750775229) ≤ (27954703 / 6250000) := by
  have h := checkLog_sound (w := (11798750775229 / 75798750775229)) (n := 12)
    (lo := (313869393 / 1000000000)) (hi := (156934697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43798750775229 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43798750775229 / 32000000000000) = 1/(500000000000 / 43798750775229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4472752473 / 1000000000) (27954703 / 6250000) (Real.log (43798750775229 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (43798750775229 / 500000000000) = -Real.log (500000000000 / 43798750775229) := by
    rw [show ((43798750775229 / 500000000000) : ℝ) = ((500000000000 / 43798750775229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4460726223 / 1000000000) ≤ -Real.log (100000000000 / 8655034144633) ∧
    -Real.log (100000000000 / 8655034144633) ≤ (446072623 / 100000000) := by
  have h := checkLog_sound (w := (2255034144633 / 15055034144633)) (n := 12)
    (lo := (301843143 / 1000000000)) (hi := (37730393 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8655034144633 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8655034144633 / 6400000000000) = 1/(100000000000 / 8655034144633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4460726223 / 1000000000) (446072623 / 100000000) (Real.log (8655034144633 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8655034144633 / 100000000000) = -Real.log (100000000000 / 8655034144633) := by
    rw [show ((8655034144633 / 100000000000) : ℝ) = ((100000000000 / 8655034144633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4467479159 / 1000000000) ≤ -Real.log (250000000000 / 21784197073859) ∧
    -Real.log (250000000000 / 21784197073859) ≤ (2233739583 / 500000000) := by
  have h := checkLog_sound (w := (5784197073859 / 37784197073859)) (n := 12)
    (lo := (308596079 / 1000000000)) (hi := (3857451 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21784197073859 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21784197073859 / 16000000000000) = 1/(250000000000 / 21784197073859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4467479159 / 1000000000) (2233739583 / 500000000) (Real.log (21784197073859 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21784197073859 / 250000000000) = -Real.log (250000000000 / 21784197073859) := by
    rw [show ((21784197073859 / 250000000000) : ℝ) = ((250000000000 / 21784197073859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044

end


