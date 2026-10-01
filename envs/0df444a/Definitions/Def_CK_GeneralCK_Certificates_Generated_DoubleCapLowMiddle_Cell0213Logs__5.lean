-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0213Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0213Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:46:32.62959+00:00
-- url     : https://prove2.me/theorems/01f30e0b-76a0-448f-af2d-042803a4246b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0217Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0217Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0217Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0213Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0214Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0215Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0216Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0217Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0213
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

theorem reflection_log_1_neg : (274241307 / 500000000) ≤ -Real.log (1600 / 2769) ∧
    -Real.log (1600 / 2769) ≤ (109696523 / 200000000) := by
  have h := checkLog_sound (w := (1169 / 4369)) (n := 12)
    (lo := (274241307 / 500000000)) (hi := (109696523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2769 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2769 / 1600) = 1/(1600 / 2769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (274241307 / 500000000) (109696523 / 200000000) (Real.log (2769 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2769 / 1600) = -Real.log (1600 / 2769) := by
    rw [show ((2769 / 1600) : ℝ) = ((1600 / 2769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1311650817 / 1000000000) ≤ -Real.log (431 / 1600) ∧
    -Real.log (431 / 1600) ≤ (1311650819 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 431) = 1/(431 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1311650819 / 1000000000) (-1311650817 / 1000000000) (Real.log (431 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272522937 / 500000000) ≤ -Real.log (3200 / 5519) ∧
    -Real.log (3200 / 5519) ≤ (4360367 / 8000000) := by
  have h := checkLog_sound (w := (2319 / 8719)) (n := 12)
    (lo := (272522937 / 500000000)) (hi := (4360367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5519 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5519 / 3200) = 1/(3200 / 5519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272522937 / 500000000) (4360367 / 8000000) (Real.log (5519 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5519 / 3200) = -Real.log (3200 / 5519) := by
    rw [show ((5519 / 3200) : ℝ) = ((3200 / 5519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (644924231 / 500000000) ≤ -Real.log (881 / 3200) ∧
    -Real.log (881 / 3200) ≤ (80615529 / 62500000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 881) = 1/(881 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80615529 / 62500000) (-644924231 / 500000000) (Real.log (881 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (379292233 / 1000000000) ≤ -Real.log (800 / 1169) ∧
    -Real.log (800 / 1169) ≤ (189646117 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1969)) (n := 12)
    (lo := (379292233 / 1000000000)) (hi := (189646117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 800) = 1/(800 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (379292233 / 1000000000) (189646117 / 500000000) (Real.log (1169 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1169 / 800) = -Real.log (800 / 1169) := by
    rw [show ((1169 / 800) : ℝ) = ((800 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (618503637 / 1000000000) ≤ -Real.log (431 / 800) ∧
    -Real.log (431 / 800) ≤ (309251819 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 431) = 1/(431 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-309251819 / 500000000) (-618503637 / 1000000000) (Real.log (431 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (371132429 / 1000000000) ≤ -Real.log (1600 / 2319) ∧
    -Real.log (1600 / 2319) ≤ (37113243 / 100000000) := by
  have h := checkLog_sound (w := (719 / 3919)) (n := 12)
    (lo := (371132429 / 1000000000)) (hi := (37113243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2319 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2319 / 1600) = 1/(1600 / 2319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (371132429 / 1000000000) (37113243 / 100000000) (Real.log (2319 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2319 / 1600) = -Real.log (1600 / 2319) := by
    rw [show ((2319 / 1600) : ℝ) = ((1600 / 2319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298350641 / 500000000) ≤ -Real.log (881 / 1600) ∧
    -Real.log (881 / 1600) ≤ (596701283 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 881) = 1/(881 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-596701283 / 1000000000) (-298350641 / 500000000) (Real.log (881 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75341867 / 125000000) ≤ -Real.log (1000000 / 1827109) ∧
    -Real.log (1000000 / 1827109) ≤ (602734937 / 1000000000) := by
  have h := checkLog_sound (w := (827109 / 2827109)) (n := 12)
    (lo := (75341867 / 125000000)) (hi := (602734937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827109 / 1000000) = 1/(1000000 / 1827109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75341867 / 125000000) (602734937 / 1000000000) (Real.log (1827109 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1827109 / 1000000) = -Real.log (1000000 / 1827109) := by
    rw [show ((1827109 / 1000000) : ℝ) = ((1000000 / 1827109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1755093939 / 1000000000) ≤ -Real.log (172891 / 1000000) ∧
    -Real.log (172891 / 1000000) ≤ (877546971 / 500000000) := by
  have h := checkLog_sound (w := (77109 / 422891)) (n := 12)
    (lo := (368799579 / 1000000000)) (hi := (18439979 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172891) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 172891) = 1/(172891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-877546971 / 500000000) (-1755093939 / 1000000000) (Real.log (172891 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302042123 / 500000000) ≤ -Real.log (125000 / 228697) ∧
    -Real.log (125000 / 228697) ≤ (604084247 / 1000000000) := by
  have h := checkLog_sound (w := (103697 / 353697)) (n := 12)
    (lo := (302042123 / 500000000)) (hi := (604084247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228697 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228697 / 125000) = 1/(125000 / 228697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302042123 / 500000000) (604084247 / 1000000000) (Real.log (228697 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (228697 / 125000) = -Real.log (125000 / 228697) := by
    rw [show ((228697 / 125000) : ℝ) = ((125000 / 228697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (442366457 / 250000000) ≤ -Real.log (21303 / 125000) ∧
    -Real.log (21303 / 125000) ≤ (1769465831 / 1000000000) := by
  have h := checkLog_sound (w := (9947 / 52553)) (n := 12)
    (lo := (95792867 / 250000000)) (hi := (383171469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 21303) = 1/(21303 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1769465831 / 1000000000) (-442366457 / 250000000) (Real.log (21303 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (146971387 / 250000000) ≤ -Real.log (500000 / 900089) ∧
    -Real.log (500000 / 900089) ≤ (587885549 / 1000000000) := by
  have h := checkLog_sound (w := (400089 / 1400089)) (n := 12)
    (lo := (146971387 / 250000000)) (hi := (587885549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900089 / 500000) = 1/(500000 / 900089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (146971387 / 250000000) (587885549 / 1000000000) (Real.log (900089 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (900089 / 500000) = -Real.log (500000 / 900089) := by
    rw [show ((900089 / 500000) : ℝ) = ((500000 / 900089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1610328307 / 1000000000) ≤ -Real.log (99911 / 500000) ∧
    -Real.log (99911 / 500000) ≤ (161032831 / 100000000) := by
  have h := checkLog_sound (w := (25089 / 224911)) (n := 12)
    (lo := (224033947 / 1000000000)) (hi := (56008487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99911) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 99911) = 1/(99911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-161032831 / 100000000) (-1610328307 / 1000000000) (Real.log (99911 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (295020117 / 500000000) ≤ -Real.log (1000000 / 1804061) ∧
    -Real.log (1000000 / 1804061) ≤ (118008047 / 200000000) := by
  have h := checkLog_sound (w := (804061 / 2804061)) (n := 12)
    (lo := (295020117 / 500000000)) (hi := (118008047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1804061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1804061 / 1000000) = 1/(1000000 / 1804061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (295020117 / 500000000) (118008047 / 200000000) (Real.log (1804061 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1804061 / 1000000) = -Real.log (1000000 / 1804061) := by
    rw [show ((1804061 / 1000000) : ℝ) = ((1000000 / 1804061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1629951891 / 1000000000) ≤ -Real.log (195939 / 1000000) ∧
    -Real.log (195939 / 1000000) ≤ (814975947 / 500000000) := by
  have h := checkLog_sound (w := (54061 / 445939)) (n := 12)
    (lo := (243657531 / 1000000000)) (hi := (60914383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195939) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 195939) = 1/(195939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-814975947 / 500000000) (-1629951891 / 1000000000) (Real.log (195939 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18862631 / 8000000) ≤ -Real.log (500000000000 / 5283991069517) ∧
    -Real.log (500000000000 / 5283991069517) ≤ (2357828879 / 1000000000) := by
  have h := checkLog_sound (w := (1283991069517 / 9283991069517)) (n := 12)
    (lo := (55677467 / 200000000)) (hi := (34798417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5283991069517 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5283991069517 / 4000000000000) = 1/(500000000000 / 5283991069517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18862631 / 8000000) (2357828879 / 1000000000) (Real.log (5283991069517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5283991069517 / 500000000000) = -Real.log (500000000000 / 5283991069517) := by
    rw [show ((5283991069517 / 500000000000) : ℝ) = ((500000000000 / 5283991069517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2373550073 / 1000000000) ≤ -Real.log (250000000000 / 2683859080881) ∧
    -Real.log (250000000000 / 2683859080881) ≤ (2373550077 / 1000000000) := by
  have h := checkLog_sound (w := (683859080881 / 4683859080881)) (n := 12)
    (lo := (294108533 / 1000000000)) (hi := (147054267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2683859080881 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2683859080881 / 2000000000000) = 1/(250000000000 / 2683859080881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2373550073 / 1000000000) (2373550077 / 1000000000) (Real.log (2683859080881 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2683859080881 / 250000000000) = -Real.log (250000000000 / 2683859080881) := by
    rw [show ((2683859080881 / 250000000000) : ℝ) = ((250000000000 / 2683859080881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (439642771 / 200000000) ≤ -Real.log (500000000000 / 4504453964027) ∧
    -Real.log (500000000000 / 4504453964027) ≤ (2198213859 / 1000000000) := by
  have h := checkLog_sound (w := (504453964027 / 8504453964027)) (n := 12)
    (lo := (23754463 / 200000000)) (hi := (29693079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4504453964027 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4504453964027 / 4000000000000) = 1/(500000000000 / 4504453964027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (439642771 / 200000000) (2198213859 / 1000000000) (Real.log (4504453964027 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4504453964027 / 500000000000) = -Real.log (500000000000 / 4504453964027) := by
    rw [show ((4504453964027 / 500000000000) : ℝ) = ((500000000000 / 4504453964027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (17759937 / 8000000) ≤ -Real.log (250000000000 / 2301814595359) ∧
    -Real.log (250000000000 / 2301814595359) ≤ (2219992129 / 1000000000) := by
  have h := checkLog_sound (w := (301814595359 / 4301814595359)) (n := 12)
    (lo := (28110117 / 200000000)) (hi := (70275293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2301814595359 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2301814595359 / 2000000000000) = 1/(250000000000 / 2301814595359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (17759937 / 8000000) (2219992129 / 1000000000) (Real.log (2301814595359 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2301814595359 / 250000000000) = -Real.log (250000000000 / 2301814595359) := by
    rw [show ((2301814595359 / 250000000000) : ℝ) = ((250000000000 / 2301814595359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0213

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0214
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

theorem reflection_log_1_neg : (272522937 / 500000000) ≤ -Real.log (3200 / 5519) ∧
    -Real.log (3200 / 5519) ≤ (4360367 / 8000000) := by
  have h := checkLog_sound (w := (2319 / 8719)) (n := 12)
    (lo := (272522937 / 500000000)) (hi := (4360367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5519 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5519 / 3200) = 1/(3200 / 5519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272522937 / 500000000) (4360367 / 8000000) (Real.log (5519 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5519 / 3200) = -Real.log (3200 / 5519) := by
    rw [show ((5519 / 3200) : ℝ) = ((3200 / 5519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (644924231 / 500000000) ≤ -Real.log (881 / 3200) ∧
    -Real.log (881 / 3200) ≤ (80615529 / 62500000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 881) = 1/(881 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80615529 / 62500000) (-644924231 / 500000000) (Real.log (881 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (371132429 / 1000000000) ≤ -Real.log (1600 / 2319) ∧
    -Real.log (1600 / 2319) ≤ (37113243 / 100000000) := by
  have h := checkLog_sound (w := (719 / 3919)) (n := 12)
    (lo := (371132429 / 1000000000)) (hi := (37113243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2319 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2319 / 1600) = 1/(1600 / 2319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (371132429 / 1000000000) (37113243 / 100000000) (Real.log (2319 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2319 / 1600) = -Real.log (1600 / 2319) := by
    rw [show ((2319 / 1600) : ℝ) = ((1600 / 2319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298350641 / 500000000) ≤ -Real.log (881 / 1600) ∧
    -Real.log (881 / 1600) ≤ (596701283 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 881) = 1/(881 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-596701283 / 1000000000) (-298350641 / 500000000) (Real.log (881 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (601416137 / 1000000000) ≤ -Real.log (1000000 / 1824701) ∧
    -Real.log (1000000 / 1824701) ≤ (300708069 / 500000000) := by
  have h := checkLog_sound (w := (824701 / 2824701)) (n := 12)
    (lo := (601416137 / 1000000000)) (hi := (300708069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1824701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1824701 / 1000000) = 1/(1000000 / 1824701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (601416137 / 1000000000) (300708069 / 500000000) (Real.log (1824701 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1824701 / 1000000) = -Real.log (1000000 / 1824701) := by
    rw [show ((1824701 / 1000000) : ℝ) = ((1000000 / 1824701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (174126219 / 100000000) ≤ -Real.log (175299 / 1000000) ∧
    -Real.log (175299 / 1000000) ≤ (1741262193 / 1000000000) := by
  have h := checkLog_sound (w := (74701 / 425299)) (n := 12)
    (lo := (35496783 / 100000000)) (hi := (354967831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175299) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 175299) = 1/(175299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1741262193 / 1000000000) (-174126219 / 100000000) (Real.log (175299 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (602735483 / 1000000000) ≤ -Real.log (100000 / 182711) ∧
    -Real.log (100000 / 182711) ≤ (150683871 / 250000000) := by
  have h := checkLog_sound (w := (82711 / 282711)) (n := 12)
    (lo := (602735483 / 1000000000)) (hi := (150683871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182711 / 100000) = 1/(100000 / 182711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (602735483 / 1000000000) (150683871 / 250000000) (Real.log (182711 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182711 / 100000) = -Real.log (100000 / 182711) := by
    rw [show ((182711 / 100000) : ℝ) = ((100000 / 182711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1755099723 / 1000000000) ≤ -Real.log (17289 / 100000) ∧
    -Real.log (17289 / 100000) ≤ (877549863 / 500000000) := by
  have h := checkLog_sound (w := (7711 / 42289)) (n := 12)
    (lo := (368805363 / 1000000000)) (hi := (92201341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17289) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 17289) = 1/(17289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-877549863 / 500000000) (-1755099723 / 1000000000) (Real.log (17289 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58573289 / 100000000) ≤ -Real.log (1000000 / 1796307) ∧
    -Real.log (1000000 / 1796307) ≤ (585732891 / 1000000000) := by
  have h := checkLog_sound (w := (796307 / 2796307)) (n := 12)
    (lo := (58573289 / 100000000)) (hi := (585732891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1796307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1796307 / 1000000) = 1/(1000000 / 1796307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58573289 / 100000000) (585732891 / 1000000000) (Real.log (1796307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1796307 / 1000000) = -Real.log (1000000 / 1796307) := by
    rw [show ((1796307 / 1000000) : ℝ) = ((1000000 / 1796307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1591141319 / 1000000000) ≤ -Real.log (203693 / 1000000) ∧
    -Real.log (203693 / 1000000) ≤ (795570661 / 500000000) := by
  have h := checkLog_sound (w := (46307 / 453693)) (n := 12)
    (lo := (204846959 / 1000000000)) (hi := (2560587 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203693) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 203693) = 1/(203693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-795570661 / 500000000) (-1591141319 / 1000000000) (Real.log (203693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73485763 / 125000000) ≤ -Real.log (1000000 / 1800179) ∧
    -Real.log (1000000 / 1800179) ≤ (117577221 / 200000000) := by
  have h := checkLog_sound (w := (800179 / 2800179)) (n := 12)
    (lo := (73485763 / 125000000)) (hi := (117577221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1800179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1800179 / 1000000) = 1/(1000000 / 1800179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73485763 / 125000000) (117577221 / 200000000) (Real.log (1800179 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1800179 / 1000000) = -Real.log (1000000 / 1800179) := by
    rw [show ((1800179 / 1000000) : ℝ) = ((1000000 / 1800179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (12580729 / 7812500) ≤ -Real.log (199821 / 1000000) ∧
    -Real.log (199821 / 1000000) ≤ (322066663 / 200000000) := by
  have h := checkLog_sound (w := (50179 / 449821)) (n := 12)
    (lo := (28004869 / 125000000)) (hi := (224038953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199821) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 199821) = 1/(199821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-322066663 / 200000000) (-12580729 / 7812500) (Real.log (199821 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2342678327 / 1000000000) ≤ -Real.log (500000000000 / 5204539101763) ∧
    -Real.log (500000000000 / 5204539101763) ≤ (2342678331 / 1000000000) := by
  have h := checkLog_sound (w := (1204539101763 / 9204539101763)) (n := 12)
    (lo := (263236787 / 1000000000)) (hi := (65809197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5204539101763 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5204539101763 / 4000000000000) = 1/(500000000000 / 5204539101763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2342678327 / 1000000000) (2342678331 / 1000000000) (Real.log (5204539101763 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5204539101763 / 500000000000) = -Real.log (500000000000 / 5204539101763) := by
    rw [show ((5204539101763 / 500000000000) : ℝ) = ((500000000000 / 5204539101763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1178917603 / 500000000) ≤ -Real.log (62500000000 / 660503065533) ∧
    -Real.log (62500000000 / 660503065533) ≤ (235783521 / 100000000) := by
  have h := checkLog_sound (w := (160503065533 / 1160503065533)) (n := 12)
    (lo := (139196833 / 500000000)) (hi := (278393667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660503065533 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(660503065533 / 500000000000) = 1/(62500000000 / 660503065533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1178917603 / 500000000) (235783521 / 100000000) (Real.log (660503065533 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (660503065533 / 62500000000) = -Real.log (62500000000 / 660503065533) := by
    rw [show ((660503065533 / 62500000000) : ℝ) = ((62500000000 / 660503065533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2176874209 / 1000000000) ≤ -Real.log (250000000000 / 2204674436529) ∧
    -Real.log (250000000000 / 2204674436529) ≤ (2176874213 / 1000000000) := by
  have h := checkLog_sound (w := (204674436529 / 4204674436529)) (n := 12)
    (lo := (97432669 / 1000000000)) (hi := (9743267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2204674436529 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2204674436529 / 2000000000000) = 1/(250000000000 / 2204674436529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2176874209 / 1000000000) (2176874213 / 1000000000) (Real.log (2204674436529 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2204674436529 / 250000000000) = -Real.log (250000000000 / 2204674436529) := by
    rw [show ((2204674436529 / 250000000000) : ℝ) = ((250000000000 / 2204674436529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (439643883 / 200000000) ≤ -Real.log (500000000000 / 4504479008713) ∧
    -Real.log (500000000000 / 4504479008713) ≤ (2198219419 / 1000000000) := by
  have h := checkLog_sound (w := (504479008713 / 8504479008713)) (n := 12)
    (lo := (950223 / 8000000)) (hi := (29694469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4504479008713 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4504479008713 / 4000000000000) = 1/(500000000000 / 4504479008713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (439643883 / 200000000) (2198219419 / 1000000000) (Real.log (4504479008713 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4504479008713 / 500000000000) = -Real.log (500000000000 / 4504479008713) := by
    rw [show ((4504479008713 / 500000000000) : ℝ) = ((500000000000 / 4504479008713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0214

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0215Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0215
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

theorem reflection_log_1_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134534189 / 250000000) ≤ -Real.log (3200 / 5481) ∧
    -Real.log (3200 / 5481) ≤ (538136757 / 1000000000) := by
  have h := checkLog_sound (w := (2281 / 8681)) (n := 12)
    (lo := (134534189 / 250000000)) (hi := (538136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5481 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5481 / 3200) = 1/(3200 / 5481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134534189 / 250000000) (538136757 / 1000000000) (Real.log (5481 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5481 / 3200) = -Real.log (3200 / 5481) := by
    rw [show ((5481 / 3200) : ℝ) = ((3200 / 5481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249523993 / 200000000) ≤ -Real.log (919 / 3200) ∧
    -Real.log (919 / 3200) ≤ (1247619967 / 1000000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 919) = 1/(919 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1247619967 / 1000000000) (-249523993 / 200000000) (Real.log (919 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177305157 / 500000000) ≤ -Real.log (1600 / 2281) ∧
    -Real.log (1600 / 2281) ≤ (70922063 / 200000000) := by
  have h := checkLog_sound (w := (681 / 3881)) (n := 12)
    (lo := (177305157 / 500000000)) (hi := (70922063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1600) = 1/(1600 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177305157 / 500000000) (70922063 / 200000000) (Real.log (2281 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2281 / 1600) = -Real.log (1600 / 2281) := by
    rw [show ((2281 / 1600) : ℝ) = ((1600 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (110894557 / 200000000) ≤ -Real.log (919 / 1600) ∧
    -Real.log (919 / 1600) ≤ (277236393 / 500000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 919) = 1/(919 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277236393 / 500000000) (-110894557 / 200000000) (Real.log (919 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (600128523 / 1000000000) ≤ -Real.log (1000000 / 1822353) ∧
    -Real.log (1000000 / 1822353) ≤ (150032131 / 250000000) := by
  have h := checkLog_sound (w := (822353 / 2822353)) (n := 12)
    (lo := (600128523 / 1000000000)) (hi := (150032131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1822353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1822353 / 1000000) = 1/(1000000 / 1822353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (600128523 / 1000000000) (150032131 / 250000000) (Real.log (1822353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1822353 / 1000000) = -Real.log (1000000 / 1822353) := by
    rw [show ((1822353 / 1000000) : ℝ) = ((1000000 / 1822353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (863978421 / 500000000) ≤ -Real.log (177647 / 1000000) ∧
    -Real.log (177647 / 1000000) ≤ (345591369 / 200000000) := by
  have h := checkLog_sound (w := (72353 / 427647)) (n := 12)
    (lo := (170831241 / 500000000)) (hi := (341662483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177647) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 177647) = 1/(177647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-345591369 / 200000000) (-863978421 / 500000000) (Real.log (177647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (300708343 / 500000000) ≤ -Real.log (500000 / 912351) ∧
    -Real.log (500000 / 912351) ≤ (601416687 / 1000000000) := by
  have h := checkLog_sound (w := (412351 / 1412351)) (n := 12)
    (lo := (300708343 / 500000000)) (hi := (601416687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912351 / 500000) = 1/(500000 / 912351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (300708343 / 500000000) (601416687 / 1000000000) (Real.log (912351 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (912351 / 500000) = -Real.log (500000 / 912351) := by
    rw [show ((912351 / 500000) : ℝ) = ((500000 / 912351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (348253579 / 200000000) ≤ -Real.log (87649 / 500000) ∧
    -Real.log (87649 / 500000) ≤ (870633949 / 500000000) := by
  have h := checkLog_sound (w := (37351 / 212649)) (n := 12)
    (lo := (70994707 / 200000000)) (hi := (11092923 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87649) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 87649) = 1/(87649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-870633949 / 500000000) (-348253579 / 200000000) (Real.log (87649 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23343269 / 40000000) ≤ -Real.log (1000000 / 1792447) ∧
    -Real.log (1000000 / 1792447) ≤ (291790863 / 500000000) := by
  have h := checkLog_sound (w := (792447 / 2792447)) (n := 12)
    (lo := (23343269 / 40000000)) (hi := (291790863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1792447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1792447 / 1000000) = 1/(1000000 / 1792447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23343269 / 40000000) (291790863 / 500000000) (Real.log (1792447 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1792447 / 1000000) = -Real.log (1000000 / 1792447) := by
    rw [show ((1792447 / 1000000) : ℝ) = ((1000000 / 1792447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1572368549 / 1000000000) ≤ -Real.log (207553 / 1000000) ∧
    -Real.log (207553 / 1000000) ≤ (196546069 / 125000000) := by
  have h := checkLog_sound (w := (42447 / 457553)) (n := 12)
    (lo := (186074189 / 1000000000)) (hi := (18607419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207553) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 207553) = 1/(207553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-196546069 / 125000000) (-1572368549 / 1000000000) (Real.log (207553 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (585733447 / 1000000000) ≤ -Real.log (250000 / 449077) ∧
    -Real.log (250000 / 449077) ≤ (73216681 / 125000000) := by
  have h := checkLog_sound (w := (199077 / 699077)) (n := 12)
    (lo := (585733447 / 1000000000)) (hi := (73216681 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449077 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449077 / 250000) = 1/(250000 / 449077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (585733447 / 1000000000) (73216681 / 125000000) (Real.log (449077 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (449077 / 250000) = -Real.log (250000 / 449077) := by
    rw [show ((449077 / 250000) : ℝ) = ((250000 / 449077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (397786557 / 250000000) ≤ -Real.log (50923 / 250000) ∧
    -Real.log (50923 / 250000) ≤ (1591146231 / 1000000000) := by
  have h := checkLog_sound (w := (11577 / 113423)) (n := 12)
    (lo := (51212967 / 250000000)) (hi := (204851869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50923) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 50923) = 1/(50923 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1591146231 / 1000000000) (-397786557 / 250000000) (Real.log (50923 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (465617073 / 200000000) ≤ -Real.log (500000000000 / 5129140936801) ∧
    -Real.log (500000000000 / 5129140936801) ≤ (2328085369 / 1000000000) := by
  have h := checkLog_sound (w := (1129140936801 / 9129140936801)) (n := 12)
    (lo := (9945753 / 40000000)) (hi := (124321913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5129140936801 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5129140936801 / 4000000000000) = 1/(500000000000 / 5129140936801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (465617073 / 200000000) (2328085369 / 1000000000) (Real.log (5129140936801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5129140936801 / 500000000000) = -Real.log (500000000000 / 5129140936801) := by
    rw [show ((5129140936801 / 500000000000) : ℝ) = ((500000000000 / 5129140936801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (117134229 / 50000000) ≤ -Real.log (125000000000 / 1301142910929) ∧
    -Real.log (125000000000 / 1301142910929) ≤ (292835573 / 125000000) := by
  have h := checkLog_sound (w := (301142910929 / 2301142910929)) (n := 12)
    (lo := (1645269 / 6250000)) (hi := (263243041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301142910929 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1301142910929 / 1000000000000) = 1/(125000000000 / 1301142910929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (117134229 / 50000000) (292835573 / 125000000) (Real.log (1301142910929 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1301142910929 / 125000000000) = -Real.log (125000000000 / 1301142910929) := by
    rw [show ((1301142910929 / 125000000000) : ℝ) = ((125000000000 / 1301142910929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2155950273 / 1000000000) ≤ -Real.log (125000000000 / 1079511618719) ∧
    -Real.log (125000000000 / 1079511618719) ≤ (2155950277 / 1000000000) := by
  have h := checkLog_sound (w := (79511618719 / 2079511618719)) (n := 12)
    (lo := (76508733 / 1000000000)) (hi := (38254367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079511618719 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1079511618719 / 1000000000000) = 1/(125000000000 / 1079511618719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2155950273 / 1000000000) (2155950277 / 1000000000) (Real.log (1079511618719 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1079511618719 / 125000000000) = -Real.log (125000000000 / 1079511618719) := by
    rw [show ((1079511618719 / 125000000000) : ℝ) = ((125000000000 / 1079511618719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (87075187 / 40000000) ≤ -Real.log (125000000000 / 1102343243721) ∧
    -Real.log (125000000000 / 1102343243721) ≤ (2176879679 / 1000000000) := by
  have h := checkLog_sound (w := (102343243721 / 2102343243721)) (n := 12)
    (lo := (19487627 / 200000000)) (hi := (12179767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102343243721 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1102343243721 / 1000000000000) = 1/(125000000000 / 1102343243721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (87075187 / 40000000) (2176879679 / 1000000000) (Real.log (1102343243721 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1102343243721 / 125000000000) = -Real.log (125000000000 / 1102343243721) := by
    rw [show ((1102343243721 / 125000000000) : ℝ) = ((125000000000 / 1102343243721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0215

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0216Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216
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

theorem reflection_log_1_neg : (134534189 / 250000000) ≤ -Real.log (3200 / 5481) ∧
    -Real.log (3200 / 5481) ≤ (538136757 / 1000000000) := by
  have h := checkLog_sound (w := (2281 / 8681)) (n := 12)
    (lo := (134534189 / 250000000)) (hi := (538136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5481 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5481 / 3200) = 1/(3200 / 5481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134534189 / 250000000) (538136757 / 1000000000) (Real.log (5481 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5481 / 3200) = -Real.log (3200 / 5481) := by
    rw [show ((5481 / 3200) : ℝ) = ((3200 / 5481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249523993 / 200000000) ≤ -Real.log (919 / 3200) ∧
    -Real.log (919 / 3200) ≤ (1247619967 / 1000000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 919) = 1/(919 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1247619967 / 1000000000) (-249523993 / 200000000) (Real.log (919 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (534664213 / 1000000000) ≤ -Real.log (1600 / 2731) ∧
    -Real.log (1600 / 2731) ≤ (267332107 / 500000000) := by
  have h := checkLog_sound (w := (1131 / 4331)) (n := 12)
    (lo := (534664213 / 1000000000)) (hi := (267332107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2731 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2731 / 1600) = 1/(1600 / 2731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (534664213 / 1000000000) (267332107 / 500000000) (Real.log (2731 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2731 / 1600) = -Real.log (1600 / 2731) := by
    rw [show ((2731 / 1600) : ℝ) = ((1600 / 2731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1227156139 / 1000000000) ≤ -Real.log (469 / 1600) ∧
    -Real.log (469 / 1600) ≤ (1227156141 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 469) = 1/(469 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1227156141 / 1000000000) (-1227156139 / 1000000000) (Real.log (469 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177305157 / 500000000) ≤ -Real.log (1600 / 2281) ∧
    -Real.log (1600 / 2281) ≤ (70922063 / 200000000) := by
  have h := checkLog_sound (w := (681 / 3881)) (n := 12)
    (lo := (177305157 / 500000000)) (hi := (70922063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1600) = 1/(1600 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177305157 / 500000000) (70922063 / 200000000) (Real.log (2281 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2281 / 1600) = -Real.log (1600 / 2281) := by
    rw [show ((2281 / 1600) : ℝ) = ((1600 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110894557 / 200000000) ≤ -Real.log (919 / 1600) ∧
    -Real.log (919 / 1600) ≤ (277236393 / 500000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 919) = 1/(919 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277236393 / 500000000) (-110894557 / 200000000) (Real.log (919 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86561437 / 250000000) ≤ -Real.log (800 / 1131) ∧
    -Real.log (800 / 1131) ≤ (346245749 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1931)) (n := 12)
    (lo := (86561437 / 250000000)) (hi := (346245749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131 / 800) = 1/(800 / 1131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86561437 / 250000000) (346245749 / 1000000000) (Real.log (1131 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1131 / 800) = -Real.log (800 / 1131) := by
    rw [show ((1131 / 800) : ℝ) = ((800 / 1131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (534008959 / 1000000000) ≤ -Real.log (469 / 800) ∧
    -Real.log (469 / 800) ≤ (834389 / 1562500) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 469) = 1/(469 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-834389 / 1562500) (-534008959 / 1000000000) (Real.log (469 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (119774333 / 200000000) ≤ -Real.log (31250 / 56877) ∧
    -Real.log (31250 / 56877) ≤ (299435833 / 500000000) := by
  have h := checkLog_sound (w := (25627 / 88127)) (n := 12)
    (lo := (119774333 / 200000000)) (hi := (299435833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56877 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56877 / 31250) = 1/(31250 / 56877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (119774333 / 200000000) (299435833 / 500000000) (Real.log (56877 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56877 / 31250) = -Real.log (31250 / 56877) := by
    rw [show ((56877 / 31250) : ℝ) = ((31250 / 56877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (343030809 / 200000000) ≤ -Real.log (5623 / 31250) ∧
    -Real.log (5623 / 31250) ≤ (13399641 / 7812500) := by
  have h := checkLog_sound (w := (4379 / 26871)) (n := 12)
    (lo := (65771937 / 200000000)) (hi := (164429843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11246) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11246) = 1/(5623 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13399641 / 7812500) (-343030809 / 200000000) (Real.log (5623 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (600129071 / 1000000000) ≤ -Real.log (500000 / 911177) ∧
    -Real.log (500000 / 911177) ≤ (37508067 / 62500000) := by
  have h := checkLog_sound (w := (411177 / 1411177)) (n := 12)
    (lo := (600129071 / 1000000000)) (hi := (37508067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911177 / 500000) = 1/(500000 / 911177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (600129071 / 1000000000) (37508067 / 62500000) (Real.log (911177 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (911177 / 500000) = -Real.log (500000 / 911177) := by
    rw [show ((911177 / 500000) : ℝ) = ((500000 / 911177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1727962471 / 1000000000) ≤ -Real.log (88823 / 500000) ∧
    -Real.log (88823 / 500000) ≤ (863981237 / 500000000) := by
  have h := checkLog_sound (w := (36177 / 213823)) (n := 12)
    (lo := (341668111 / 1000000000)) (hi := (21354257 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 88823) = 1/(88823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-863981237 / 500000000) (-1727962471 / 1000000000) (Real.log (88823 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72679009 / 125000000) ≤ -Real.log (500000 / 894299) ∧
    -Real.log (500000 / 894299) ≤ (581432073 / 1000000000) := by
  have h := checkLog_sound (w := (394299 / 1394299)) (n := 12)
    (lo := (72679009 / 125000000)) (hi := (581432073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894299 / 500000) = 1/(500000 / 894299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72679009 / 125000000) (581432073 / 1000000000) (Real.log (894299 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (894299 / 500000) = -Real.log (500000 / 894299) := by
    rw [show ((894299 / 500000) : ℝ) = ((500000 / 894299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1553993743 / 1000000000) ≤ -Real.log (105701 / 500000) ∧
    -Real.log (105701 / 500000) ≤ (776996873 / 500000000) := by
  have h := checkLog_sound (w := (19299 / 230701)) (n := 12)
    (lo := (167699383 / 1000000000)) (hi := (20962423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105701) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 105701) = 1/(105701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-776996873 / 500000000) (-1553993743 / 1000000000) (Real.log (105701 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (583582283 / 1000000000) ≤ -Real.log (15625 / 28007) ∧
    -Real.log (15625 / 28007) ≤ (145895571 / 250000000) := by
  have h := checkLog_sound (w := (6191 / 21816)) (n := 12)
    (lo := (583582283 / 1000000000)) (hi := (145895571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28007 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28007 / 15625) = 1/(15625 / 28007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (583582283 / 1000000000) (145895571 / 250000000) (Real.log (28007 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (28007 / 15625) = -Real.log (15625 / 28007) := by
    rw [show ((28007 / 15625) : ℝ) = ((15625 / 28007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1572373367 / 1000000000) ≤ -Real.log (3243 / 15625) ∧
    -Real.log (3243 / 15625) ≤ (157237337 / 100000000) := by
  have h := checkLog_sound (w := (2653 / 28597)) (n := 12)
    (lo := (186079007 / 1000000000)) (hi := (5814969 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12972) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 12972) = 1/(3243 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-157237337 / 100000000) (-1572373367 / 1000000000) (Real.log (3243 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (231402571 / 100000000) ≤ -Real.log (500000000000 / 5057531566779) ∧
    -Real.log (500000000000 / 5057531566779) ≤ (1157012857 / 500000000) := by
  have h := checkLog_sound (w := (1057531566779 / 9057531566779)) (n := 12)
    (lo := (23458417 / 100000000)) (hi := (234584171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5057531566779 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5057531566779 / 4000000000000) = 1/(500000000000 / 5057531566779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (231402571 / 100000000) (1157012857 / 500000000) (Real.log (5057531566779 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5057531566779 / 500000000000) = -Real.log (500000000000 / 5057531566779) := by
    rw [show ((5057531566779 / 500000000000) : ℝ) = ((500000000000 / 5057531566779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2328091543 / 1000000000) ≤ -Real.log (31250000000 / 320573289013) ∧
    -Real.log (31250000000 / 320573289013) ≤ (2328091547 / 1000000000) := by
  have h := checkLog_sound (w := (70573289013 / 570573289013)) (n := 12)
    (lo := (248650003 / 1000000000)) (hi := (62162501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320573289013 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320573289013 / 250000000000) = 1/(31250000000 / 320573289013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2328091543 / 1000000000) (2328091547 / 1000000000) (Real.log (320573289013 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (320573289013 / 31250000000) = -Real.log (31250000000 / 320573289013) := by
    rw [show ((320573289013 / 31250000000) : ℝ) = ((31250000000 / 320573289013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (427085163 / 200000000) ≤ -Real.log (500000000000 / 4230324216421) ∧
    -Real.log (500000000000 / 4230324216421) ≤ (2135425819 / 1000000000) := by
  have h := checkLog_sound (w := (230324216421 / 8230324216421)) (n := 12)
    (lo := (2239371 / 40000000)) (hi := (13996069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4230324216421 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4230324216421 / 4000000000000) = 1/(500000000000 / 4230324216421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (427085163 / 200000000) (2135425819 / 1000000000) (Real.log (4230324216421 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4230324216421 / 500000000000) = -Real.log (500000000000 / 4230324216421) := by
    rw [show ((4230324216421 / 500000000000) : ℝ) = ((500000000000 / 4230324216421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2155955649 / 1000000000) ≤ -Real.log (6250000000 / 53975871107) ∧
    -Real.log (6250000000 / 53975871107) ≤ (2155955653 / 1000000000) := by
  have h := checkLog_sound (w := (3975871107 / 103975871107)) (n := 12)
    (lo := (76514109 / 1000000000)) (hi := (7651411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53975871107 / 50000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(53975871107 / 50000000000) = 1/(6250000000 / 53975871107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2155955649 / 1000000000) (2155955653 / 1000000000) (Real.log (53975871107 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (53975871107 / 6250000000) = -Real.log (6250000000 / 53975871107) := by
    rw [show ((53975871107 / 6250000000) : ℝ) = ((6250000000 / 53975871107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0217Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217
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

theorem reflection_log_1_neg : (534664213 / 1000000000) ≤ -Real.log (1600 / 2731) ∧
    -Real.log (1600 / 2731) ≤ (267332107 / 500000000) := by
  have h := checkLog_sound (w := (1131 / 4331)) (n := 12)
    (lo := (534664213 / 1000000000)) (hi := (267332107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2731 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2731 / 1600) = 1/(1600 / 2731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (534664213 / 1000000000) (267332107 / 500000000) (Real.log (2731 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2731 / 1600) = -Real.log (1600 / 2731) := by
    rw [show ((2731 / 1600) : ℝ) = ((1600 / 2731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1227156139 / 1000000000) ≤ -Real.log (469 / 1600) ∧
    -Real.log (469 / 1600) ≤ (1227156141 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 469) = 1/(469 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1227156141 / 1000000000) (-1227156139 / 1000000000) (Real.log (469 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (531179569 / 1000000000) ≤ -Real.log (3200 / 5443) ∧
    -Real.log (3200 / 5443) ≤ (53117957 / 100000000) := by
  have h := checkLog_sound (w := (2243 / 8643)) (n := 12)
    (lo := (531179569 / 1000000000)) (hi := (53117957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5443 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5443 / 3200) = 1/(3200 / 5443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (531179569 / 1000000000) (53117957 / 100000000) (Real.log (5443 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5443 / 3200) = -Real.log (3200 / 5443) := by
    rw [show ((5443 / 3200) : ℝ) = ((3200 / 5443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150887837 / 125000000) ≤ -Real.log (957 / 3200) ∧
    -Real.log (957 / 3200) ≤ (603551349 / 500000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 957) = 1/(957 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-603551349 / 500000000) (-150887837 / 125000000) (Real.log (957 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86561437 / 250000000) ≤ -Real.log (800 / 1131) ∧
    -Real.log (800 / 1131) ≤ (346245749 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1931)) (n := 12)
    (lo := (86561437 / 250000000)) (hi := (346245749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131 / 800) = 1/(800 / 1131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86561437 / 250000000) (346245749 / 1000000000) (Real.log (1131 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1131 / 800) = -Real.log (800 / 1131) := by
    rw [show ((1131 / 800) : ℝ) = ((800 / 1131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (534008959 / 1000000000) ≤ -Real.log (469 / 800) ∧
    -Real.log (469 / 800) ≤ (834389 / 1562500) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 469) = 1/(469 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-834389 / 1562500) (-534008959 / 1000000000) (Real.log (469 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168905313 / 500000000) ≤ -Real.log (1600 / 2243) ∧
    -Real.log (1600 / 2243) ≤ (337810627 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 3843)) (n := 12)
    (lo := (168905313 / 500000000)) (hi := (337810627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2243 / 1600) = 1/(1600 / 2243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168905313 / 500000000) (337810627 / 1000000000) (Real.log (2243 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2243 / 1600) = -Real.log (1600 / 2243) := by
    rw [show ((2243 / 1600) : ℝ) = ((1600 / 2243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128488879 / 250000000) ≤ -Real.log (957 / 1600) ∧
    -Real.log (957 / 1600) ≤ (513955517 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 957) = 1/(957 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-513955517 / 1000000000) (-128488879 / 250000000) (Real.log (957 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298823391 / 500000000) ≤ -Real.log (250000 / 454459) ∧
    -Real.log (250000 / 454459) ≤ (597646783 / 1000000000) := by
  have h := checkLog_sound (w := (204459 / 704459)) (n := 12)
    (lo := (298823391 / 500000000)) (hi := (597646783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454459 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454459 / 250000) = 1/(250000 / 454459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298823391 / 500000000) (597646783 / 1000000000) (Real.log (454459 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (454459 / 250000) = -Real.log (250000 / 454459) := by
    rw [show ((454459 / 250000) : ℝ) = ((250000 / 454459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1702847897 / 1000000000) ≤ -Real.log (45541 / 250000) ∧
    -Real.log (45541 / 250000) ≤ (17028479 / 10000000) := by
  have h := checkLog_sound (w := (16959 / 108041)) (n := 12)
    (lo := (316553537 / 1000000000)) (hi := (158276769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45541) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 45541) = 1/(45541 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17028479 / 10000000) (-1702847897 / 1000000000) (Real.log (45541 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (299436107 / 500000000) ≤ -Real.log (200000 / 364013) ∧
    -Real.log (200000 / 364013) ≤ (119774443 / 200000000) := by
  have h := checkLog_sound (w := (164013 / 564013)) (n := 12)
    (lo := (299436107 / 500000000)) (hi := (119774443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364013 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364013 / 200000) = 1/(200000 / 364013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (299436107 / 500000000) (119774443 / 200000000) (Real.log (364013 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (364013 / 200000) = -Real.log (200000 / 364013) := by
    rw [show ((364013 / 200000) : ℝ) = ((200000 / 364013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1715159603 / 1000000000) ≤ -Real.log (35987 / 200000) ∧
    -Real.log (35987 / 200000) ≤ (857579803 / 500000000) := by
  have h := checkLog_sound (w := (14013 / 85987)) (n := 12)
    (lo := (328865243 / 1000000000)) (hi := (82216311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35987) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 35987) = 1/(35987 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-857579803 / 500000000) (-1715159603 / 1000000000) (Real.log (35987 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (579282831 / 1000000000) ≤ -Real.log (500000 / 892379) ∧
    -Real.log (500000 / 892379) ≤ (36205177 / 62500000) := by
  have h := checkLog_sound (w := (392379 / 1392379)) (n := 12)
    (lo := (579282831 / 1000000000)) (hi := (36205177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892379 / 500000) = 1/(500000 / 892379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (579282831 / 1000000000) (36205177 / 62500000) (Real.log (892379 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (892379 / 500000) = -Real.log (500000 / 892379) := by
    rw [show ((892379 / 500000) : ℝ) = ((500000 / 892379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1535992301 / 1000000000) ≤ -Real.log (107621 / 500000) ∧
    -Real.log (107621 / 500000) ≤ (95999519 / 62500000) := by
  have h := checkLog_sound (w := (17379 / 232621)) (n := 12)
    (lo := (149697941 / 1000000000)) (hi := (74848971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107621) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 107621) = 1/(107621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-95999519 / 62500000) (-1535992301 / 1000000000) (Real.log (107621 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (581432631 / 1000000000) ≤ -Real.log (1000000 / 1788599) ∧
    -Real.log (1000000 / 1788599) ≤ (72679079 / 125000000) := by
  have h := checkLog_sound (w := (788599 / 2788599)) (n := 12)
    (lo := (581432631 / 1000000000)) (hi := (72679079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1788599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1788599 / 1000000) = 1/(1000000 / 1788599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (581432631 / 1000000000) (72679079 / 125000000) (Real.log (1788599 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1788599 / 1000000) = -Real.log (1000000 / 1788599) := by
    rw [show ((1788599 / 1000000) : ℝ) = ((1000000 / 1788599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (776999237 / 500000000) ≤ -Real.log (211401 / 1000000) ∧
    -Real.log (211401 / 1000000) ≤ (1553998477 / 1000000000) := by
  have h := checkLog_sound (w := (38599 / 461401)) (n := 12)
    (lo := (83852057 / 500000000)) (hi := (33540823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211401) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 211401) = 1/(211401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1553998477 / 1000000000) (-776999237 / 500000000) (Real.log (211401 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2300494679 / 1000000000) ≤ -Real.log (10000000000 / 99791177181) ∧
    -Real.log (10000000000 / 99791177181) ≤ (2300494683 / 1000000000) := by
  have h := checkLog_sound (w := (19791177181 / 179791177181)) (n := 12)
    (lo := (221053139 / 1000000000)) (hi := (11052657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99791177181 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(99791177181 / 80000000000) = 1/(10000000000 / 99791177181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2300494679 / 1000000000) (2300494683 / 1000000000) (Real.log (99791177181 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99791177181 / 10000000000) = -Real.log (10000000000 / 99791177181) := by
    rw [show ((99791177181 / 10000000000) : ℝ) = ((10000000000 / 99791177181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2314031817 / 1000000000) ≤ -Real.log (500000000000 / 5057562453109) ∧
    -Real.log (500000000000 / 5057562453109) ≤ (2314031821 / 1000000000) := by
  have h := checkLog_sound (w := (1057562453109 / 9057562453109)) (n := 12)
    (lo := (234590277 / 1000000000)) (hi := (117295139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5057562453109 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5057562453109 / 4000000000000) = 1/(500000000000 / 5057562453109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2314031817 / 1000000000) (2314031821 / 1000000000) (Real.log (5057562453109 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5057562453109 / 500000000000) = -Real.log (500000000000 / 5057562453109) := by
    rw [show ((5057562453109 / 500000000000) : ℝ) = ((500000000000 / 5057562453109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (528818783 / 250000000) ≤ -Real.log (250000000000 / 2072966707241) ∧
    -Real.log (250000000000 / 2072966707241) ≤ (16525587 / 7812500) := by
  have h := checkLog_sound (w := (72966707241 / 4072966707241)) (n := 12)
    (lo := (4479199 / 125000000)) (hi := (35833593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2072966707241 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2072966707241 / 2000000000000) = 1/(250000000000 / 2072966707241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (528818783 / 250000000) (16525587 / 7812500) (Real.log (2072966707241 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2072966707241 / 250000000000) = -Real.log (250000000000 / 2072966707241) := by
    rw [show ((2072966707241 / 250000000000) : ℝ) = ((250000000000 / 2072966707241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (427086221 / 200000000) ≤ -Real.log (100000000000 / 846069318499) ∧
    -Real.log (100000000000 / 846069318499) ≤ (2135431109 / 1000000000) := by
  have h := checkLog_sound (w := (46069318499 / 1646069318499)) (n := 12)
    (lo := (11197913 / 200000000)) (hi := (27994783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846069318499 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(846069318499 / 800000000000) = 1/(100000000000 / 846069318499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (427086221 / 200000000) (2135431109 / 1000000000) (Real.log (846069318499 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (846069318499 / 100000000000) = -Real.log (100000000000 / 846069318499) := by
    rw [show ((846069318499 / 100000000000) : ℝ) = ((100000000000 / 846069318499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217

end


