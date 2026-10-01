-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0036Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0036Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:47:45.712419+00:00
-- url     : https://prove2.me/theorems/88967b5a-7a32-4cad-a29a-d327d06af3c7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0036Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0037Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0038Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0039Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036
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

theorem reflection_log_1_neg : (680375539 / 1000000000) ≤ -Real.log (102400 / 202201) ∧
    -Real.log (102400 / 202201) ≤ (34018777 / 50000000) := by
  have h := checkLog_sound (w := (99801 / 304601)) (n := 12)
    (lo := (680375539 / 1000000000)) (hi := (34018777 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202201 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202201 / 102400) = 1/(102400 / 202201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680375539 / 1000000000) (34018777 / 50000000) (Real.log (202201 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202201 / 102400) = -Real.log (102400 / 202201) := by
    rw [show ((202201 / 102400) : ℝ) = ((102400 / 202201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1836879977 / 500000000) ≤ -Real.log (2599 / 102400) ∧
    -Real.log (2599 / 102400) ≤ (91843999 / 25000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2599) = 1/(2599 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) (Real.log (2599 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680281569 / 1000000000) ≤ -Real.log (51200 / 101091) ∧
    -Real.log (51200 / 101091) ≤ (68028157 / 100000000) := by
  have h := checkLog_sound (w := (49891 / 152291)) (n := 12)
    (lo := (680281569 / 1000000000)) (hi := (68028157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101091 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101091 / 51200) = 1/(51200 / 101091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680281569 / 1000000000) (68028157 / 100000000) (Real.log (101091 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101091 / 51200) = -Real.log (51200 / 101091) := by
    rw [show ((101091 / 51200) : ℝ) = ((51200 / 101091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1833238021 / 500000000) ≤ -Real.log (1309 / 51200) ∧
    -Real.log (1309 / 51200) ≤ (229154753 / 62500000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1309) = 1/(1309 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) (Real.log (1309 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667438671 / 1000000000) ≤ -Real.log (51200 / 99801) ∧
    -Real.log (51200 / 99801) ≤ (41714917 / 62500000) := by
  have h := checkLog_sound (w := (48601 / 151001)) (n := 12)
    (lo := (667438671 / 1000000000)) (hi := (41714917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99801 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99801 / 51200) = 1/(51200 / 99801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667438671 / 1000000000) (41714917 / 62500000) (Real.log (99801 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99801 / 51200) = -Real.log (51200 / 99801) := by
    rw [show ((99801 / 51200) : ℝ) = ((51200 / 99801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1490306387 / 500000000) ≤ -Real.log (2599 / 51200) ∧
    -Real.log (2599 / 51200) ≤ (2980612779 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2599) = 1/(2599 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) (Real.log (2599 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (333624137 / 500000000) ≤ -Real.log (25600 / 49891) ∧
    -Real.log (25600 / 49891) ≤ (26689931 / 40000000) := by
  have h := checkLog_sound (w := (24291 / 75491)) (n := 12)
    (lo := (333624137 / 500000000)) (hi := (26689931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49891 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49891 / 25600) = 1/(25600 / 49891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (333624137 / 500000000) (26689931 / 40000000) (Real.log (49891 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49891 / 25600) = -Real.log (25600 / 49891) := by
    rw [show ((49891 / 25600) : ℝ) = ((25600 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1486664431 / 500000000) ≤ -Real.log (1309 / 25600) ∧
    -Real.log (1309 / 25600) ≤ (2973328867 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1309) = 1/(1309 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) (Real.log (1309 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341161909 / 500000000) ≤ -Real.log (100000 / 197847) ∧
    -Real.log (100000 / 197847) ≤ (682323819 / 1000000000) := by
  have h := checkLog_sound (w := (97847 / 297847)) (n := 12)
    (lo := (341161909 / 500000000)) (hi := (682323819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197847 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197847 / 100000) = 1/(100000 / 197847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341161909 / 500000000) (682323819 / 1000000000) (Real.log (197847 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197847 / 100000) = -Real.log (100000 / 197847) := by
    rw [show ((197847 / 100000) : ℝ) = ((100000 / 197847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (959576991 / 250000000) ≤ -Real.log (2153 / 100000) ∧
    -Real.log (2153 / 100000) ≤ (383830797 / 100000000) := by
  have h := checkLog_sound (w := (486 / 2639)) (n := 12)
    (lo := (11642877 / 31250000)) (hi := (74514413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2153) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2153) = 1/(2153 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-383830797 / 100000000) (-959576991 / 250000000) (Real.log (2153 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42649977 / 62500000) ≤ -Real.log (50000 / 98931) ∧
    -Real.log (50000 / 98931) ≤ (682399633 / 1000000000) := by
  have h := checkLog_sound (w := (48931 / 148931)) (n := 12)
    (lo := (42649977 / 62500000)) (hi := (682399633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98931 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98931 / 50000) = 1/(50000 / 98931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42649977 / 62500000) (682399633 / 1000000000) (Real.log (98931 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98931 / 50000) = -Real.log (50000 / 98931) := by
    rw [show ((98931 / 50000) : ℝ) = ((50000 / 98931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (384529937 / 100000000) ≤ -Real.log (1069 / 50000) ∧
    -Real.log (1069 / 50000) ≤ (240331211 / 62500000) := by
  have h := checkLog_sound (w := (987 / 5263)) (n := 12)
    (lo := (37956347 / 100000000)) (hi := (379563471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2138) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2138) = 1/(1069 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-240331211 / 62500000) (-384529937 / 100000000) (Real.log (1069 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136453947 / 200000000) ≤ -Real.log (1000000 / 1978363) ∧
    -Real.log (1000000 / 1978363) ≤ (85283717 / 125000000) := by
  have h := checkLog_sound (w := (978363 / 2978363)) (n := 12)
    (lo := (136453947 / 200000000)) (hi := (85283717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978363 / 1000000) = 1/(1000000 / 1978363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136453947 / 200000000) (85283717 / 125000000) (Real.log (1978363 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978363 / 1000000) = -Real.log (1000000 / 1978363) := by
    rw [show ((1978363 / 1000000) : ℝ) = ((1000000 / 1978363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3833350463 / 1000000000) ≤ -Real.log (21637 / 1000000) ∧
    -Real.log (21637 / 1000000) ≤ (3833350469 / 1000000000) := by
  have h := checkLog_sound (w := (9613 / 52887)) (n := 12)
    (lo := (367614563 / 1000000000)) (hi := (91903641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21637) = 1/(21637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3833350469 / 1000000000) (-3833350463 / 1000000000) (Real.log (21637 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170586767 / 250000000) ≤ -Real.log (250000 / 494629) ∧
    -Real.log (250000 / 494629) ≤ (682347069 / 1000000000) := by
  have h := checkLog_sound (w := (244629 / 744629)) (n := 12)
    (lo := (170586767 / 250000000)) (hi := (682347069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494629 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494629 / 250000) = 1/(250000 / 494629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170586767 / 250000000) (682347069 / 1000000000) (Real.log (494629 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494629 / 250000) = -Real.log (250000 / 494629) := by
    rw [show ((494629 / 250000) : ℝ) = ((250000 / 494629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (960111701 / 250000000) ≤ -Real.log (5371 / 250000) ∧
    -Real.log (5371 / 250000) ≤ (384044681 / 100000000) := by
  have h := checkLog_sound (w := (4883 / 26367)) (n := 12)
    (lo := (46838863 / 125000000)) (hi := (74942181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10742) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10742) = 1/(5371 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-384044681 / 100000000) (-960111701 / 250000000) (Real.log (5371 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2260315891 / 500000000) ≤ -Real.log (25000000000 / 2297340919647) ∧
    -Real.log (25000000000 / 2297340919647) ≤ (4520631789 / 1000000000) := by
  have h := checkLog_sound (w := (697340919647 / 3897340919647)) (n := 12)
    (lo := (180874351 / 500000000)) (hi := (361748703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2297340919647 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2297340919647 / 1600000000000) = 1/(25000000000 / 2297340919647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2260315891 / 500000000) (4520631789 / 1000000000) (Real.log (2297340919647 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2297340919647 / 25000000000) = -Real.log (25000000000 / 2297340919647) := by
    rw [show ((2297340919647 / 25000000000) : ℝ) = ((25000000000 / 2297340919647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2263849501 / 500000000) ≤ -Real.log (100000000000 / 9254536950421) ∧
    -Real.log (100000000000 / 9254536950421) ≤ (4527699009 / 1000000000) := by
  have h := checkLog_sound (w := (2854536950421 / 15654536950421)) (n := 12)
    (lo := (184407961 / 500000000)) (hi := (368815923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9254536950421 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9254536950421 / 6400000000000) = 1/(100000000000 / 9254536950421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2263849501 / 500000000) (4527699009 / 1000000000) (Real.log (9254536950421 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9254536950421 / 100000000000) = -Real.log (100000000000 / 9254536950421) := by
    rw [show ((9254536950421 / 100000000000) : ℝ) = ((100000000000 / 9254536950421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2257810099 / 500000000) ≤ -Real.log (500000000000 / 45717128067661) ∧
    -Real.log (500000000000 / 45717128067661) ≤ (903124041 / 200000000) := by
  have h := checkLog_sound (w := (13717128067661 / 77717128067661)) (n := 12)
    (lo := (178368559 / 500000000)) (hi := (356737119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45717128067661 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45717128067661 / 32000000000000) = 1/(500000000000 / 45717128067661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2257810099 / 500000000) (903124041 / 200000000) (Real.log (45717128067661 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45717128067661 / 500000000000) = -Real.log (500000000000 / 45717128067661) := by
    rw [show ((45717128067661 / 500000000000) : ℝ) = ((500000000000 / 45717128067661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (282674617 / 62500000) ≤ -Real.log (125000000000 / 11511566747347) ∧
    -Real.log (125000000000 / 11511566747347) ≤ (4522793879 / 1000000000) := by
  have h := checkLog_sound (w := (3511566747347 / 19511566747347)) (n := 12)
    (lo := (45488849 / 125000000)) (hi := (363910793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11511566747347 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11511566747347 / 8000000000000) = 1/(125000000000 / 11511566747347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (282674617 / 62500000) (4522793879 / 1000000000) (Real.log (11511566747347 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11511566747347 / 125000000000) = -Real.log (125000000000 / 11511566747347) := by
    rw [show ((11511566747347 / 125000000000) : ℝ) = ((125000000000 / 11511566747347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037
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

theorem reflection_log_1_neg : (680281569 / 1000000000) ≤ -Real.log (51200 / 101091) ∧
    -Real.log (51200 / 101091) ≤ (68028157 / 100000000) := by
  have h := checkLog_sound (w := (49891 / 152291)) (n := 12)
    (lo := (680281569 / 1000000000)) (hi := (68028157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101091 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101091 / 51200) = 1/(51200 / 101091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680281569 / 1000000000) (68028157 / 100000000) (Real.log (101091 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101091 / 51200) = -Real.log (51200 / 101091) := by
    rw [show ((101091 / 51200) : ℝ) = ((51200 / 101091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1833238021 / 500000000) ≤ -Real.log (1309 / 51200) ∧
    -Real.log (1309 / 51200) ≤ (229154753 / 62500000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1309) = 1/(1309 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) (Real.log (1309 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68018759 / 100000000) ≤ -Real.log (102400 / 202163) ∧
    -Real.log (102400 / 202163) ≤ (680187591 / 1000000000) := by
  have h := checkLog_sound (w := (99763 / 304563)) (n := 12)
    (lo := (68018759 / 100000000)) (hi := (680187591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202163 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202163 / 102400) = 1/(102400 / 202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68018759 / 100000000) (680187591 / 1000000000) (Real.log (202163 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202163 / 102400) = -Real.log (102400 / 202163) := by
    rw [show ((202163 / 102400) : ℝ) = ((102400 / 202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1829622401 / 500000000) ≤ -Real.log (2637 / 102400) ∧
    -Real.log (2637 / 102400) ≤ (457405601 / 125000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2637) = 1/(2637 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) (Real.log (2637 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (333624137 / 500000000) ≤ -Real.log (25600 / 49891) ∧
    -Real.log (25600 / 49891) ≤ (26689931 / 40000000) := by
  have h := checkLog_sound (w := (24291 / 75491)) (n := 12)
    (lo := (333624137 / 500000000)) (hi := (26689931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49891 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49891 / 25600) = 1/(25600 / 49891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (333624137 / 500000000) (26689931 / 40000000) (Real.log (49891 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49891 / 25600) = -Real.log (25600 / 49891) := by
    rw [show ((49891 / 25600) : ℝ) = ((25600 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1486664431 / 500000000) ≤ -Real.log (1309 / 25600) ∧
    -Real.log (1309 / 25600) ≤ (2973328867 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1309) = 1/(1309 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) (Real.log (1309 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667057841 / 1000000000) ≤ -Real.log (51200 / 99763) ∧
    -Real.log (51200 / 99763) ≤ (333528921 / 500000000) := by
  have h := checkLog_sound (w := (48563 / 150963)) (n := 12)
    (lo := (667057841 / 1000000000)) (hi := (333528921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99763 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99763 / 51200) = 1/(51200 / 99763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667057841 / 1000000000) (333528921 / 500000000) (Real.log (99763 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99763 / 51200) = -Real.log (51200 / 99763) := by
    rw [show ((99763 / 51200) : ℝ) = ((51200 / 99763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1483048811 / 500000000) ≤ -Real.log (2637 / 51200) ∧
    -Real.log (2637 / 51200) ≤ (2966097627 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2637) = 1/(2637 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) (Real.log (2637 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682247999 / 1000000000) ≤ -Real.log (12500 / 24729) ∧
    -Real.log (12500 / 24729) ≤ (85281 / 125000) := by
  have h := checkLog_sound (w := (12229 / 37229)) (n := 12)
    (lo := (682247999 / 1000000000)) (hi := (85281 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24729 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24729 / 12500) = 1/(12500 / 24729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682247999 / 1000000000) (85281 / 125000) (Real.log (24729 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (24729 / 12500) = -Real.log (12500 / 24729) := by
    rw [show ((24729 / 12500) : ℝ) = ((12500 / 24729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3831365099 / 1000000000) ≤ -Real.log (271 / 12500) ∧
    -Real.log (271 / 12500) ≤ (766273021 / 200000000) := by
  have h := checkLog_sound (w := (957 / 5293)) (n := 12)
    (lo := (365629199 / 1000000000)) (hi := (914073 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2168) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2168) = 1/(271 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-766273021 / 200000000) (-3831365099 / 1000000000) (Real.log (271 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170581081 / 250000000) ≤ -Real.log (1000000 / 1978471) ∧
    -Real.log (1000000 / 1978471) ≤ (27292973 / 40000000) := by
  have h := checkLog_sound (w := (978471 / 2978471)) (n := 12)
    (lo := (170581081 / 250000000)) (hi := (27292973 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978471 / 1000000) = 1/(1000000 / 1978471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170581081 / 250000000) (27292973 / 40000000) (Real.log (1978471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978471 / 1000000) = -Real.log (1000000 / 1978471) := by
    rw [show ((1978471 / 1000000) : ℝ) = ((1000000 / 1978471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (959588603 / 250000000) ≤ -Real.log (21529 / 1000000) ∧
    -Real.log (21529 / 1000000) ≤ (1919177209 / 500000000) := by
  have h := checkLog_sound (w := (9721 / 52779)) (n := 12)
    (lo := (23288657 / 62500000)) (hi := (372618513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21529) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21529) = 1/(21529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1919177209 / 500000000) (-959588603 / 250000000) (Real.log (21529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341096703 / 500000000) ≤ -Real.log (250000 / 494553) ∧
    -Real.log (250000 / 494553) ≤ (682193407 / 1000000000) := by
  have h := checkLog_sound (w := (244553 / 744553)) (n := 12)
    (lo := (341096703 / 500000000)) (hi := (682193407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494553 / 250000) = 1/(250000 / 494553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341096703 / 500000000) (682193407 / 1000000000) (Real.log (494553 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (494553 / 250000) = -Real.log (250000 / 494553) := by
    rw [show ((494553 / 250000) : ℝ) = ((250000 / 494553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (956598979 / 250000000) ≤ -Real.log (5447 / 250000) ∧
    -Real.log (5447 / 250000) ≤ (1913197961 / 500000000) := by
  have h := checkLog_sound (w := (4731 / 26519)) (n := 12)
    (lo := (22541251 / 62500000)) (hi := (360660017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10894) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10894) = 1/(5447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1913197961 / 500000000) (-956598979 / 250000000) (Real.log (5447 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4264189 / 6250000) ≤ -Real.log (250000 / 494591) ∧
    -Real.log (250000 / 494591) ≤ (682270241 / 1000000000) := by
  have h := checkLog_sound (w := (244591 / 744591)) (n := 12)
    (lo := (4264189 / 6250000)) (hi := (682270241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494591 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494591 / 250000) = 1/(250000 / 494591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4264189 / 6250000) (682270241 / 1000000000) (Real.log (494591 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494591 / 250000) = -Real.log (250000 / 494591) := by
    rw [show ((494591 / 250000) : ℝ) = ((250000 / 494591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1916698341 / 500000000) ≤ -Real.log (5409 / 250000) ∧
    -Real.log (5409 / 250000) ≤ (239587293 / 62500000) := by
  have h := checkLog_sound (w := (4807 / 26443)) (n := 12)
    (lo := (183830391 / 500000000)) (hi := (367660783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10818) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10818) = 1/(5409 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-239587293 / 62500000) (-1916698341 / 500000000) (Real.log (5409 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2256806549 / 500000000) ≤ -Real.log (125000000000 / 11406365313653) ∧
    -Real.log (125000000000 / 11406365313653) ≤ (902722621 / 200000000) := by
  have h := checkLog_sound (w := (3406365313653 / 19406365313653)) (n := 12)
    (lo := (177365009 / 500000000)) (hi := (354730019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11406365313653 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11406365313653 / 8000000000000) = 1/(125000000000 / 11406365313653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2256806549 / 500000000) (902722621 / 200000000) (Real.log (11406365313653 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11406365313653 / 125000000000) = -Real.log (125000000000 / 11406365313653) := by
    rw [show ((11406365313653 / 125000000000) : ℝ) = ((125000000000 / 11406365313653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (282542421 / 62500000) ≤ -Real.log (125000000000 / 11487243950021) ∧
    -Real.log (125000000000 / 11487243950021) ≤ (4520678743 / 1000000000) := by
  have h := checkLog_sound (w := (3487243950021 / 19487243950021)) (n := 12)
    (lo := (45224457 / 125000000)) (hi := (361795657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11487243950021 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11487243950021 / 8000000000000) = 1/(125000000000 / 11487243950021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (282542421 / 62500000) (4520678743 / 1000000000) (Real.log (11487243950021 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11487243950021 / 125000000000) = -Real.log (125000000000 / 11487243950021) := by
    rw [show ((11487243950021 / 125000000000) : ℝ) = ((125000000000 / 11487243950021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2254294661 / 500000000) ≤ -Real.log (500000000000 / 45396823939783) ∧
    -Real.log (500000000000 / 45396823939783) ≤ (4508589329 / 1000000000) := by
  have h := checkLog_sound (w := (13396823939783 / 77396823939783)) (n := 12)
    (lo := (174853121 / 500000000)) (hi := (349706243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45396823939783 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45396823939783 / 32000000000000) = 1/(500000000000 / 45396823939783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2254294661 / 500000000) (4508589329 / 1000000000) (Real.log (45396823939783 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45396823939783 / 500000000000) = -Real.log (500000000000 / 45396823939783) := by
    rw [show ((45396823939783 / 500000000000) : ℝ) = ((500000000000 / 45396823939783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2257833461 / 500000000) ≤ -Real.log (100000000000 / 9143852837863) ∧
    -Real.log (100000000000 / 9143852837863) ≤ (4515666929 / 1000000000) := by
  have h := checkLog_sound (w := (2743852837863 / 15543852837863)) (n := 12)
    (lo := (178391921 / 500000000)) (hi := (356783843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9143852837863 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9143852837863 / 6400000000000) = 1/(100000000000 / 9143852837863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2257833461 / 500000000) (4515666929 / 1000000000) (Real.log (9143852837863 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9143852837863 / 100000000000) = -Real.log (100000000000 / 9143852837863) := by
    rw [show ((9143852837863 / 100000000000) : ℝ) = ((100000000000 / 9143852837863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038
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

theorem reflection_log_1_neg : (68018759 / 100000000) ≤ -Real.log (102400 / 202163) ∧
    -Real.log (102400 / 202163) ≤ (680187591 / 1000000000) := by
  have h := checkLog_sound (w := (99763 / 304563)) (n := 12)
    (lo := (68018759 / 100000000)) (hi := (680187591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202163 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202163 / 102400) = 1/(102400 / 202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68018759 / 100000000) (680187591 / 1000000000) (Real.log (202163 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202163 / 102400) = -Real.log (102400 / 202163) := by
    rw [show ((202163 / 102400) : ℝ) = ((102400 / 202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1829622401 / 500000000) ≤ -Real.log (2637 / 102400) ∧
    -Real.log (2637 / 102400) ≤ (457405601 / 125000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2637) = 1/(2637 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) (Real.log (2637 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (340046801 / 500000000) ≤ -Real.log (3200 / 6317) ∧
    -Real.log (3200 / 6317) ≤ (680093603 / 1000000000) := by
  have h := checkLog_sound (w := (3117 / 9517)) (n := 12)
    (lo := (340046801 / 500000000)) (hi := (680093603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6317 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6317 / 3200) = 1/(3200 / 6317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (340046801 / 500000000) (680093603 / 1000000000) (Real.log (6317 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6317 / 3200) = -Real.log (3200 / 6317) := by
    rw [show ((6317 / 3200) : ℝ) = ((3200 / 6317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1826032739 / 500000000) ≤ -Real.log (83 / 3200) ∧
    -Real.log (83 / 3200) ≤ (913016371 / 250000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(100 / 83) = 1/(83 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) (Real.log (83 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667057841 / 1000000000) ≤ -Real.log (51200 / 99763) ∧
    -Real.log (51200 / 99763) ≤ (333528921 / 500000000) := by
  have h := checkLog_sound (w := (48563 / 150963)) (n := 12)
    (lo := (667057841 / 1000000000)) (hi := (333528921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99763 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99763 / 51200) = 1/(51200 / 99763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667057841 / 1000000000) (333528921 / 500000000) (Real.log (99763 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99763 / 51200) = -Real.log (51200 / 99763) := by
    rw [show ((99763 / 51200) : ℝ) = ((51200 / 99763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1483048811 / 500000000) ≤ -Real.log (2637 / 51200) ∧
    -Real.log (2637 / 51200) ≤ (2966097627 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2637) = 1/(2637 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) (Real.log (2637 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (666867371 / 1000000000) ≤ -Real.log (1600 / 3117) ∧
    -Real.log (1600 / 3117) ≤ (166716843 / 250000000) := by
  have h := checkLog_sound (w := (1517 / 4717)) (n := 12)
    (lo := (666867371 / 1000000000)) (hi := (166716843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 1600) = 1/(1600 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (666867371 / 1000000000) (166716843 / 250000000) (Real.log (3117 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3117 / 1600) = -Real.log (1600 / 3117) := by
    rw [show ((3117 / 1600) : ℝ) = ((1600 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1479459149 / 500000000) ≤ -Real.log (83 / 1600) ∧
    -Real.log (83 / 1600) ≤ (2958918303 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 83) = 1/(83 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) (Real.log (83 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17054317 / 25000000) ≤ -Real.log (1000000 / 1978171) ∧
    -Real.log (1000000 / 1978171) ≤ (682172681 / 1000000000) := by
  have h := checkLog_sound (w := (978171 / 2978171)) (n := 12)
    (lo := (17054317 / 25000000)) (hi := (682172681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978171 / 1000000) = 1/(1000000 / 1978171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17054317 / 25000000) (682172681 / 1000000000) (Real.log (1978171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978171 / 1000000) = -Real.log (1000000 / 1978171) := by
    rw [show ((1978171 / 1000000) : ℝ) = ((1000000 / 1978171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (764903183 / 200000000) ≤ -Real.log (21829 / 1000000) ∧
    -Real.log (21829 / 1000000) ≤ (3824515921 / 1000000000) := by
  have h := checkLog_sound (w := (9421 / 53079)) (n := 12)
    (lo := (71756003 / 200000000)) (hi := (22423751 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21829) = 1/(21829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3824515921 / 1000000000) (-764903183 / 200000000) (Real.log (21829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136449701 / 200000000) ≤ -Real.log (1000000 / 1978321) ∧
    -Real.log (1000000 / 1978321) ≤ (341124253 / 500000000) := by
  have h := checkLog_sound (w := (978321 / 2978321)) (n := 12)
    (lo := (136449701 / 200000000)) (hi := (341124253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978321 / 1000000) = 1/(1000000 / 1978321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136449701 / 200000000) (341124253 / 500000000) (Real.log (1978321 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978321 / 1000000) = -Real.log (1000000 / 1978321) := by
    rw [show ((1978321 / 1000000) : ℝ) = ((1000000 / 1978321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1915705613 / 500000000) ≤ -Real.log (21679 / 1000000) ∧
    -Real.log (21679 / 1000000) ≤ (119731601 / 31250000) := by
  have h := checkLog_sound (w := (9571 / 52929)) (n := 12)
    (lo := (182837663 / 500000000)) (hi := (365675327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21679) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21679) = 1/(21679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-119731601 / 31250000) (-1915705613 / 500000000) (Real.log (21679 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682117071 / 1000000000) ≤ -Real.log (1000000 / 1978061) ∧
    -Real.log (1000000 / 1978061) ≤ (42632317 / 62500000) := by
  have h := checkLog_sound (w := (978061 / 2978061)) (n := 12)
    (lo := (682117071 / 1000000000)) (hi := (42632317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978061 / 1000000) = 1/(1000000 / 1978061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682117071 / 1000000000) (42632317 / 62500000) (Real.log (1978061 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978061 / 1000000) = -Real.log (1000000 / 1978061) := by
    rw [show ((1978061 / 1000000) : ℝ) = ((1000000 / 1978061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3819489401 / 1000000000) ≤ -Real.log (21939 / 1000000) ∧
    -Real.log (21939 / 1000000) ≤ (3819489407 / 1000000000) := by
  have h := checkLog_sound (w := (9311 / 53189)) (n := 12)
    (lo := (353753501 / 1000000000)) (hi := (176876751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21939) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21939) = 1/(21939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3819489407 / 1000000000) (-3819489401 / 1000000000) (Real.log (21939 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682193911 / 1000000000) ≤ -Real.log (1000000 / 1978213) ∧
    -Real.log (1000000 / 1978213) ≤ (85274239 / 125000000) := by
  have h := checkLog_sound (w := (978213 / 2978213)) (n := 12)
    (lo := (682193911 / 1000000000)) (hi := (85274239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978213 / 1000000) = 1/(1000000 / 1978213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682193911 / 1000000000) (85274239 / 125000000) (Real.log (1978213 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978213 / 1000000) = -Real.log (1000000 / 1978213) := by
    rw [show ((1978213 / 1000000) : ℝ) = ((1000000 / 1978213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1913220907 / 500000000) ≤ -Real.log (21787 / 1000000) ∧
    -Real.log (21787 / 1000000) ≤ (191322091 / 50000000) := by
  have h := checkLog_sound (w := (9463 / 53037)) (n := 12)
    (lo := (180352957 / 500000000)) (hi := (72141183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21787) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21787) = 1/(21787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-191322091 / 50000000) (-1913220907 / 500000000) (Real.log (21787 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (901337719 / 200000000) ≤ -Real.log (500000000000 / 45310618901461) ∧
    -Real.log (500000000000 / 45310618901461) ≤ (2253344301 / 500000000) := by
  have h := checkLog_sound (w := (13310618901461 / 77310618901461)) (n := 12)
    (lo := (69561103 / 200000000)) (hi := (86951379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45310618901461 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45310618901461 / 32000000000000) = 1/(500000000000 / 45310618901461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (901337719 / 200000000) (2253344301 / 500000000) (Real.log (45310618901461 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45310618901461 / 500000000000) = -Real.log (500000000000 / 45310618901461) := by
    rw [show ((45310618901461 / 500000000000) : ℝ) = ((500000000000 / 45310618901461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (451365973 / 100000000) ≤ -Real.log (31250000000 / 2851724306933) ∧
    -Real.log (31250000000 / 2851724306933) ≤ (4513659737 / 1000000000) := by
  have h := checkLog_sound (w := (851724306933 / 4851724306933)) (n := 12)
    (lo := (7095533 / 20000000)) (hi := (354776651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2851724306933 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2851724306933 / 2000000000000) = 1/(31250000000 / 2851724306933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (451365973 / 100000000) (4513659737 / 1000000000) (Real.log (2851724306933 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2851724306933 / 31250000000) = -Real.log (31250000000 / 2851724306933) := by
    rw [show ((2851724306933 / 31250000000) : ℝ) = ((31250000000 / 2851724306933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (562700809 / 125000000) ≤ -Real.log (500000000000 / 45080928939331) ∧
    -Real.log (500000000000 / 45080928939331) ≤ (4501606479 / 1000000000) := by
  have h := checkLog_sound (w := (13080928939331 / 77080928939331)) (n := 12)
    (lo := (5355053 / 15625000)) (hi := (342723393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45080928939331 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45080928939331 / 32000000000000) = 1/(500000000000 / 45080928939331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (562700809 / 125000000) (4501606479 / 1000000000) (Real.log (45080928939331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45080928939331 / 500000000000) = -Real.log (500000000000 / 45080928939331) := by
    rw [show ((45080928939331 / 500000000000) : ℝ) = ((500000000000 / 45080928939331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (180345429 / 40000000) ≤ -Real.log (500000000000 / 45398930554919) ∧
    -Real.log (500000000000 / 45398930554919) ≤ (1127158933 / 250000000) := by
  have h := checkLog_sound (w := (13398930554919 / 77398930554919)) (n := 12)
    (lo := (69950529 / 200000000)) (hi := (174876323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45398930554919 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45398930554919 / 32000000000000) = 1/(500000000000 / 45398930554919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (180345429 / 40000000) (1127158933 / 250000000) (Real.log (45398930554919 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45398930554919 / 500000000000) = -Real.log (500000000000 / 45398930554919) := by
    rw [show ((45398930554919 / 500000000000) : ℝ) = ((500000000000 / 45398930554919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039
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

theorem reflection_log_1_neg : (340046801 / 500000000) ≤ -Real.log (3200 / 6317) ∧
    -Real.log (3200 / 6317) ≤ (680093603 / 1000000000) := by
  have h := checkLog_sound (w := (3117 / 9517)) (n := 12)
    (lo := (340046801 / 500000000)) (hi := (680093603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6317 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6317 / 3200) = 1/(3200 / 6317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (340046801 / 500000000) (680093603 / 1000000000) (Real.log (6317 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6317 / 3200) = -Real.log (3200 / 6317) := by
    rw [show ((6317 / 3200) : ℝ) = ((3200 / 6317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1826032739 / 500000000) ≤ -Real.log (83 / 3200) ∧
    -Real.log (83 / 3200) ≤ (913016371 / 250000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(100 / 83) = 1/(83 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) (Real.log (83 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135999921 / 200000000) ≤ -Real.log (4096 / 8085) ∧
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


theorem reflection_log_3 : Bounds (135999921 / 200000000) (339999803 / 500000000) (Real.log (8085 / 4096)) := by
  have h := reflection_log_3_neg
  have he : Real.log (8085 / 4096) = -Real.log (4096 / 8085) := by
    rw [show ((8085 / 4096) : ℝ) = ((4096 / 8085) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3644937329 / 1000000000) ≤ -Real.log (107 / 4096) ∧
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


theorem reflection_log_4 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) (Real.log (107 / 4096)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (666867371 / 1000000000) ≤ -Real.log (1600 / 3117) ∧
    -Real.log (1600 / 3117) ≤ (166716843 / 250000000) := by
  have h := checkLog_sound (w := (1517 / 4717)) (n := 12)
    (lo := (666867371 / 1000000000)) (hi := (166716843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 1600) = 1/(1600 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (666867371 / 1000000000) (166716843 / 250000000) (Real.log (3117 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3117 / 1600) = -Real.log (1600 / 3117) := by
    rw [show ((3117 / 1600) : ℝ) = ((1600 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1479459149 / 500000000) ≤ -Real.log (83 / 1600) ∧
    -Real.log (83 / 1600) ≤ (2958918303 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 83) = 1/(83 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) (Real.log (83 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (133335373 / 200000000) ≤ -Real.log (2048 / 3989) ∧
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


theorem reflection_log_7 : Bounds (133335373 / 200000000) (333338433 / 500000000) (Real.log (3989 / 2048)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3989 / 2048) = -Real.log (2048 / 3989) := by
    rw [show ((3989 / 2048) : ℝ) = ((2048 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2951790149 / 1000000000) ≤ -Real.log (107 / 2048) ∧
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


theorem reflection_log_8 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) (Real.log (107 / 2048)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136419471 / 200000000) ≤ -Real.log (500000 / 989011) ∧
    -Real.log (500000 / 989011) ≤ (170524339 / 250000000) := by
  have h := checkLog_sound (w := (489011 / 1489011)) (n := 12)
    (lo := (136419471 / 200000000)) (hi := (170524339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989011 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989011 / 500000) = 1/(500000 / 989011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136419471 / 200000000) (170524339 / 250000000) (Real.log (989011 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989011 / 500000) = -Real.log (500000 / 989011) := by
    rw [show ((989011 / 500000) : ℝ) = ((500000 / 989011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3817713323 / 1000000000) ≤ -Real.log (10989 / 500000) ∧
    -Real.log (10989 / 500000) ≤ (3817713329 / 1000000000) := by
  have h := checkLog_sound (w := (2318 / 13307)) (n := 12)
    (lo := (351977423 / 1000000000)) (hi := (21998589 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10989) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10989) = 1/(10989 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3817713329 / 1000000000) (-3817713323 / 1000000000) (Real.log (10989 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136434637 / 200000000) ≤ -Real.log (250000 / 494543) ∧
    -Real.log (250000 / 494543) ≤ (341086593 / 500000000) := by
  have h := checkLog_sound (w := (244543 / 744543)) (n := 12)
    (lo := (136434637 / 200000000)) (hi := (341086593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494543 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494543 / 250000) = 1/(250000 / 494543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136434637 / 200000000) (341086593 / 500000000) (Real.log (494543 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494543 / 250000) = -Real.log (250000 / 494543) := by
    rw [show ((494543 / 250000) : ℝ) = ((250000 / 494543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1912280863 / 500000000) ≤ -Real.log (5457 / 250000) ∧
    -Real.log (5457 / 250000) ≤ (956140433 / 250000000) := by
  have h := checkLog_sound (w := (4711 / 26539)) (n := 12)
    (lo := (179412913 / 500000000)) (hi := (358825827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10914) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10914) = 1/(5457 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-956140433 / 250000000) (-1912280863 / 500000000) (Real.log (5457 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682040731 / 1000000000) ≤ -Real.log (100000 / 197791) ∧
    -Real.log (100000 / 197791) ≤ (170510183 / 250000000) := by
  have h := checkLog_sound (w := (97791 / 297791)) (n := 12)
    (lo := (682040731 / 1000000000)) (hi := (170510183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197791 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197791 / 100000) = 1/(100000 / 197791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682040731 / 1000000000) (170510183 / 250000000) (Real.log (197791 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (197791 / 100000) = -Real.log (100000 / 197791) := by
    rw [show ((197791 / 100000) : ℝ) = ((100000 / 197791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1906315129 / 500000000) ≤ -Real.log (2209 / 100000) ∧
    -Real.log (2209 / 100000) ≤ (476578783 / 125000000) := by
  have h := checkLog_sound (w := (458 / 2667)) (n := 12)
    (lo := (173447179 / 500000000)) (hi := (346894359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2209) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2209) = 1/(2209 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-476578783 / 125000000) (-1906315129 / 500000000) (Real.log (2209 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682117577 / 1000000000) ≤ -Real.log (500000 / 989031) ∧
    -Real.log (500000 / 989031) ≤ (341058789 / 500000000) := by
  have h := checkLog_sound (w := (489031 / 1489031)) (n := 12)
    (lo := (682117577 / 1000000000)) (hi := (341058789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989031 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989031 / 500000) = 1/(500000 / 989031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682117577 / 1000000000) (341058789 / 500000000) (Real.log (989031 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (989031 / 500000) = -Real.log (500000 / 989031) := by
    rw [show ((989031 / 500000) : ℝ) = ((500000 / 989031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3819534983 / 1000000000) ≤ -Real.log (10969 / 500000) ∧
    -Real.log (10969 / 500000) ≤ (3819534989 / 1000000000) := by
  have h := checkLog_sound (w := (2328 / 13297)) (n := 12)
    (lo := (353799083 / 1000000000)) (hi := (88449771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10969) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10969) = 1/(10969 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3819534989 / 1000000000) (-3819534983 / 1000000000) (Real.log (10969 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2249905339 / 500000000) ≤ -Real.log (100000000000 / 9000009100009) ∧
    -Real.log (100000000000 / 9000009100009) ≤ (899962137 / 200000000) := by
  have h := checkLog_sound (w := (2600009100009 / 15400009100009)) (n := 12)
    (lo := (170463799 / 500000000)) (hi := (340927599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9000009100009 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9000009100009 / 6400000000000) = 1/(100000000000 / 9000009100009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2249905339 / 500000000) (899962137 / 200000000) (Real.log (9000009100009 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9000009100009 / 100000000000) = -Real.log (100000000000 / 9000009100009) := by
    rw [show ((9000009100009 / 100000000000) : ℝ) = ((100000000000 / 9000009100009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (70417733 / 15625000) ≤ -Real.log (500000000000 / 45312717610409) ∧
    -Real.log (500000000000 / 45312717610409) ≤ (4506734919 / 1000000000) := by
  have h := checkLog_sound (w := (13312717610409 / 77312717610409)) (n := 12)
    (lo := (43481479 / 125000000)) (hi := (347851833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45312717610409 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45312717610409 / 32000000000000) = 1/(500000000000 / 45312717610409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (70417733 / 15625000) (4506734919 / 1000000000) (Real.log (45312717610409 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45312717610409 / 500000000000) = -Real.log (500000000000 / 45312717610409) := by
    rw [show ((45312717610409 / 500000000000) : ℝ) = ((500000000000 / 45312717610409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4494670989 / 1000000000) ≤ -Real.log (500000000000 / 44769352648257) ∧
    -Real.log (500000000000 / 44769352648257) ≤ (1123667749 / 250000000) := by
  have h := checkLog_sound (w := (12769352648257 / 76769352648257)) (n := 12)
    (lo := (335787909 / 1000000000)) (hi := (33578791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44769352648257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44769352648257 / 32000000000000) = 1/(500000000000 / 44769352648257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4494670989 / 1000000000) (1123667749 / 250000000) (Real.log (44769352648257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44769352648257 / 500000000000) = -Real.log (500000000000 / 44769352648257) := by
    rw [show ((44769352648257 / 500000000000) : ℝ) = ((500000000000 / 44769352648257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (56270657 / 12500000) ≤ -Real.log (500000000000 / 45083006655119) ∧
    -Real.log (500000000000 / 45083006655119) ≤ (4501652567 / 1000000000) := by
  have h := checkLog_sound (w := (13083006655119 / 77083006655119)) (n := 12)
    (lo := (8569237 / 25000000)) (hi := (342769481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45083006655119 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45083006655119 / 32000000000000) = 1/(500000000000 / 45083006655119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (56270657 / 12500000) (4501652567 / 1000000000) (Real.log (45083006655119 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45083006655119 / 500000000000) = -Real.log (500000000000 / 45083006655119) := by
    rw [show ((45083006655119 / 500000000000) : ℝ) = ((500000000000 / 45083006655119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039

end


