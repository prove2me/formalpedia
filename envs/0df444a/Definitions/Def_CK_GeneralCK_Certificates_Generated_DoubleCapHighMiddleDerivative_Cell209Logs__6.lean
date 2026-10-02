-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell209Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell209Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:49:10.167544+00:00
-- url     : https://prove2.me/theorems/17a508e0-4e71-420d-9acf-85c15b11346d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell209Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell210…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell209Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell210Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell211Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell212Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell209Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell210Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell211Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell212Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell209Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell210Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell211Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell212Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell209Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell210Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell211Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell212Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell213Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell214Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell209Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell209
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (158516133 / 500000000) ≤ -Real.log (512 / 703) ∧
    -Real.log (512 / 703) ≤ (317032267 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1215)) (n := 12)
    (lo := (158516133 / 500000000)) (hi := (317032267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 512) = 1/(512 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (158516133 / 500000000) (317032267 / 1000000000) (Real.log (703 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (703 / 512) = -Real.log (512 / 703) := by
    rw [show ((703 / 512) : ℝ) = ((512 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (466883501 / 1000000000) ≤ -Real.log (321 / 512) ∧
    -Real.log (321 / 512) ≤ (233441751 / 500000000) := by
  have h := checkLog_sound (w := (191 / 833)) (n := 12)
    (lo := (466883501 / 1000000000)) (hi := (233441751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 321) = 1/(321 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-233441751 / 500000000) (-466883501 / 1000000000) (Real.log (321 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (316605433 / 1000000000) ≤ -Real.log (5120 / 7027) ∧
    -Real.log (5120 / 7027) ≤ (158302717 / 500000000) := by
  have h := checkLog_sound (w := (1907 / 12147)) (n := 12)
    (lo := (316605433 / 1000000000)) (hi := (158302717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027 / 5120) = 1/(5120 / 7027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (316605433 / 1000000000) (158302717 / 500000000) (Real.log (7027 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7027 / 5120) = -Real.log (5120 / 7027) := by
    rw [show ((7027 / 5120) : ℝ) = ((5120 / 7027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232974679 / 500000000) ≤ -Real.log (3213 / 5120) ∧
    -Real.log (3213 / 5120) ≤ (465949359 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 8333)) (n := 12)
    (lo := (232974679 / 500000000)) (hi := (465949359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3213) = 1/(3213 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-465949359 / 1000000000) (-232974679 / 500000000) (Real.log (3213 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117530527 / 500000000) ≤ -Real.log (500000 / 632493) ∧
    -Real.log (500000 / 632493) ≤ (47012211 / 200000000) := by
  have h := checkLog_sound (w := (132493 / 1132493)) (n := 12)
    (lo := (117530527 / 500000000)) (hi := (47012211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632493 / 500000) = 1/(500000 / 632493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117530527 / 500000000) (47012211 / 200000000) (Real.log (632493 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (632493 / 500000) = -Real.log (500000 / 632493) := by
    rw [show ((632493 / 500000) : ℝ) = ((500000 / 632493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (76966433 / 250000000) ≤ -Real.log (367507 / 500000) ∧
    -Real.log (367507 / 500000) ≤ (307865733 / 1000000000) := by
  have h := checkLog_sound (w := (132493 / 867507)) (n := 12)
    (lo := (76966433 / 250000000)) (hi := (307865733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367507) = 1/(367507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307865733 / 1000000000) (-76966433 / 250000000) (Real.log (367507 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23539539 / 100000000) ≤ -Real.log (1000000 / 1265409) ∧
    -Real.log (1000000 / 1265409) ≤ (235395391 / 1000000000) := by
  have h := checkLog_sound (w := (265409 / 2265409)) (n := 12)
    (lo := (23539539 / 100000000)) (hi := (235395391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265409 / 1000000) = 1/(1000000 / 1265409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23539539 / 100000000) (235395391 / 1000000000) (Real.log (1265409 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1265409 / 1000000) = -Real.log (1000000 / 1265409) := by
    rw [show ((1265409 / 1000000) : ℝ) = ((1000000 / 1265409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (308441397 / 1000000000) ≤ -Real.log (734591 / 1000000) ∧
    -Real.log (734591 / 1000000) ≤ (154220699 / 500000000) := by
  have h := checkLog_sound (w := (265409 / 1734591)) (n := 12)
    (lo := (308441397 / 1000000000)) (hi := (154220699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734591) = 1/(734591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154220699 / 500000000) (-308441397 / 1000000000) (Real.log (734591 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (87434427 / 500000000) ≤ -Real.log (100000 / 119109) ∧
    -Real.log (100000 / 119109) ≤ (34973771 / 200000000) := by
  have h := checkLog_sound (w := (19109 / 219109)) (n := 12)
    (lo := (87434427 / 500000000)) (hi := (34973771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119109 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119109 / 100000) = 1/(100000 / 119109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (87434427 / 500000000) (34973771 / 200000000) (Real.log (119109 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119109 / 100000) = -Real.log (100000 / 119109) := by
    rw [show ((119109 / 100000) : ℝ) = ((100000 / 119109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6627113 / 31250000) ≤ -Real.log (80891 / 100000) ∧
    -Real.log (80891 / 100000) ≤ (212067617 / 1000000000) := by
  have h := checkLog_sound (w := (19109 / 180891)) (n := 12)
    (lo := (6627113 / 31250000)) (hi := (212067617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80891) = 1/(80891 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-212067617 / 1000000000) (-6627113 / 31250000) (Real.log (80891 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175134961 / 1000000000) ≤ -Real.log (1000000 / 1191407) ∧
    -Real.log (1000000 / 1191407) ≤ (87567481 / 500000000) := by
  have h := checkLog_sound (w := (191407 / 2191407)) (n := 12)
    (lo := (175134961 / 1000000000)) (hi := (87567481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191407 / 1000000) = 1/(1000000 / 1191407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175134961 / 1000000000) (87567481 / 500000000) (Real.log (1191407 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1191407 / 1000000) = -Real.log (1000000 / 1191407) := by
    rw [show ((1191407 / 1000000) : ℝ) = ((1000000 / 1191407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106229789 / 500000000) ≤ -Real.log (808593 / 1000000) ∧
    -Real.log (808593 / 1000000) ≤ (212459579 / 1000000000) := by
  have h := checkLog_sound (w := (191407 / 1808593)) (n := 12)
    (lo := (106229789 / 500000000)) (hi := (212459579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808593) = 1/(808593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-212459579 / 1000000000) (-106229789 / 500000000) (Real.log (808593 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (782554791 / 1000000000) ≤ -Real.log (31250000000 / 68345393713) ∧
    -Real.log (31250000000 / 68345393713) ≤ (782554793 / 1000000000) := by
  have h := checkLog_sound (w := (5845393713 / 130845393713)) (n := 12)
    (lo := (89407611 / 1000000000)) (hi := (22351903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68345393713 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68345393713 / 62500000000) = 1/(31250000000 / 68345393713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (782554791 / 1000000000) (782554793 / 1000000000) (Real.log (68345393713 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (68345393713 / 31250000000) = -Real.log (31250000000 / 68345393713) := by
    rw [show ((68345393713 / 31250000000) : ℝ) = ((31250000000 / 68345393713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97989471 / 125000000) ≤ -Real.log (125000000000 / 273753894081) ∧
    -Real.log (125000000000 / 273753894081) ≤ (78391577 / 100000000) := by
  have h := checkLog_sound (w := (23753894081 / 523753894081)) (n := 12)
    (lo := (22692147 / 250000000)) (hi := (90768589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273753894081 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273753894081 / 250000000000) = 1/(125000000000 / 273753894081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (97989471 / 125000000) (78391577 / 100000000) (Real.log (273753894081 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (273753894081 / 125000000000) = -Real.log (125000000000 / 273753894081) := by
    rw [show ((273753894081 / 125000000000) : ℝ) = ((125000000000 / 273753894081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (542926787 / 1000000000) ≤ -Real.log (125000000000 / 215129575763) ∧
    -Real.log (125000000000 / 215129575763) ≤ (135731697 / 250000000) := by
  have h := checkLog_sound (w := (90129575763 / 340129575763)) (n := 12)
    (lo := (542926787 / 1000000000)) (hi := (135731697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215129575763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215129575763 / 125000000000) = 1/(125000000000 / 215129575763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (542926787 / 1000000000) (135731697 / 250000000) (Real.log (215129575763 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (215129575763 / 125000000000) = -Real.log (125000000000 / 215129575763) := by
    rw [show ((215129575763 / 125000000000) : ℝ) = ((125000000000 / 215129575763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (543836787 / 1000000000) ≤ -Real.log (15625000000 / 26915679099) ∧
    -Real.log (15625000000 / 26915679099) ≤ (135959197 / 250000000) := by
  have h := checkLog_sound (w := (11290679099 / 42540679099)) (n := 12)
    (lo := (543836787 / 1000000000)) (hi := (135959197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26915679099 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26915679099 / 15625000000) = 1/(15625000000 / 26915679099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (543836787 / 1000000000) (135959197 / 250000000) (Real.log (26915679099 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (26915679099 / 15625000000) = -Real.log (15625000000 / 26915679099) := by
    rw [show ((26915679099 / 15625000000) : ℝ) = ((15625000000 / 26915679099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38693647 / 100000000) ≤ -Real.log (25000000000 / 36811573599) ∧
    -Real.log (25000000000 / 36811573599) ≤ (386936471 / 1000000000) := by
  have h := checkLog_sound (w := (11811573599 / 61811573599)) (n := 12)
    (lo := (38693647 / 100000000)) (hi := (386936471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36811573599 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36811573599 / 25000000000) = 1/(25000000000 / 36811573599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38693647 / 100000000) (386936471 / 1000000000) (Real.log (36811573599 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36811573599 / 25000000000) = -Real.log (25000000000 / 36811573599) := by
    rw [show ((36811573599 / 25000000000) : ℝ) = ((25000000000 / 36811573599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (19379727 / 50000000) ≤ -Real.log (100000000000 / 147343224589) ∧
    -Real.log (100000000000 / 147343224589) ≤ (387594541 / 1000000000) := by
  have h := checkLog_sound (w := (47343224589 / 247343224589)) (n := 12)
    (lo := (19379727 / 50000000)) (hi := (387594541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147343224589 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147343224589 / 100000000000) = 1/(100000000000 / 147343224589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (19379727 / 50000000) (387594541 / 1000000000) (Real.log (147343224589 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (147343224589 / 100000000000) = -Real.log (100000000000 / 147343224589) := by
    rw [show ((147343224589 / 100000000000) : ℝ) = ((100000000000 / 147343224589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37324617 / 1000000000) ≤ -Real.log (963363360351 / 1000000000000) ∧
    -Real.log (963363360351 / 1000000000000) ≤ (18662309 / 500000000) := by
  have h := checkLog_sound (w := (36636639649 / 1963363360351)) (n := 12)
    (lo := (37324617 / 1000000000)) (hi := (18662309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963363360351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963363360351) = 1/(963363360351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18662309 / 500000000) (-37324617 / 1000000000) (Real.log (963363360351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18599381 / 500000000) ≤ -Real.log (9634846119 / 10000000000) ∧
    -Real.log (9634846119 / 10000000000) ≤ (37198763 / 1000000000) := by
  have h := checkLog_sound (w := (365153881 / 19634846119)) (n := 12)
    (lo := (18599381 / 500000000)) (hi := (37198763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9634846119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9634846119) = 1/(9634846119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-37198763 / 1000000000) (-18599381 / 500000000) (Real.log (9634846119 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell209

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell210Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell210
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (158729459 / 500000000) ≤ -Real.log (5120 / 7033) ∧
    -Real.log (5120 / 7033) ≤ (317458919 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 12153)) (n := 12)
    (lo := (158729459 / 500000000)) (hi := (317458919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7033 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7033 / 5120) = 1/(5120 / 7033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (158729459 / 500000000) (317458919 / 1000000000) (Real.log (7033 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7033 / 5120) = -Real.log (5120 / 7033) := by
    rw [show ((7033 / 5120) : ℝ) = ((5120 / 7033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (233909259 / 500000000) ≤ -Real.log (3207 / 5120) ∧
    -Real.log (3207 / 5120) ≤ (467818519 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 8327)) (n := 12)
    (lo := (233909259 / 500000000)) (hi := (467818519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3207) = 1/(3207 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-467818519 / 1000000000) (-233909259 / 500000000) (Real.log (3207 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158516133 / 500000000) ≤ -Real.log (512 / 703) ∧
    -Real.log (512 / 703) ≤ (317032267 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1215)) (n := 12)
    (lo := (158516133 / 500000000)) (hi := (317032267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 512) = 1/(512 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158516133 / 500000000) (317032267 / 1000000000) (Real.log (703 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (703 / 512) = -Real.log (512 / 703) := by
    rw [show ((703 / 512) : ℝ) = ((512 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (466883501 / 1000000000) ≤ -Real.log (321 / 512) ∧
    -Real.log (321 / 512) ≤ (233441751 / 500000000) := by
  have h := checkLog_sound (w := (191 / 833)) (n := 12)
    (lo := (466883501 / 1000000000)) (hi := (233441751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 321) = 1/(321 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-233441751 / 500000000) (-466883501 / 1000000000) (Real.log (321 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235394599 / 1000000000) ≤ -Real.log (15625 / 19772) ∧
    -Real.log (15625 / 19772) ≤ (1176973 / 5000000) := by
  have h := checkLog_sound (w := (4147 / 35397)) (n := 12)
    (lo := (235394599 / 1000000000)) (hi := (1176973 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19772 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19772 / 15625) = 1/(15625 / 19772) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235394599 / 1000000000) (1176973 / 5000000) (Real.log (19772 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19772 / 15625) = -Real.log (15625 / 19772) := by
    rw [show ((19772 / 15625) : ℝ) = ((15625 / 19772) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (61688007 / 200000000) ≤ -Real.log (11478 / 15625) ∧
    -Real.log (11478 / 15625) ≤ (77110009 / 250000000) := by
  have h := checkLog_sound (w := (4147 / 27103)) (n := 12)
    (lo := (61688007 / 200000000)) (hi := (77110009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11478) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11478) = 1/(11478 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77110009 / 250000000) (-61688007 / 200000000) (Real.log (11478 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (235729613 / 1000000000) ≤ -Real.log (125000 / 158229) ∧
    -Real.log (125000 / 158229) ≤ (117864807 / 500000000) := by
  have h := checkLog_sound (w := (33229 / 283229)) (n := 12)
    (lo := (235729613 / 1000000000)) (hi := (117864807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158229 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158229 / 125000) = 1/(125000 / 158229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (235729613 / 1000000000) (117864807 / 500000000) (Real.log (158229 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158229 / 125000) = -Real.log (125000 / 158229) := by
    rw [show ((158229 / 125000) : ℝ) = ((125000 / 158229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (309017393 / 1000000000) ≤ -Real.log (91771 / 125000) ∧
    -Real.log (91771 / 125000) ≤ (154508697 / 500000000) := by
  have h := checkLog_sound (w := (33229 / 216771)) (n := 12)
    (lo := (309017393 / 1000000000)) (hi := (154508697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91771) = 1/(91771 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154508697 / 500000000) (-309017393 / 1000000000) (Real.log (91771 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (87567061 / 500000000) ≤ -Real.log (500000 / 595703) ∧
    -Real.log (500000 / 595703) ≤ (175134123 / 1000000000) := by
  have h := checkLog_sound (w := (95703 / 1095703)) (n := 12)
    (lo := (87567061 / 500000000)) (hi := (175134123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595703 / 500000) = 1/(500000 / 595703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (87567061 / 500000000) (175134123 / 1000000000) (Real.log (595703 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (595703 / 500000) = -Real.log (500000 / 595703) := by
    rw [show ((595703 / 500000) : ℝ) = ((500000 / 595703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (106229171 / 500000000) ≤ -Real.log (404297 / 500000) ∧
    -Real.log (404297 / 500000) ≤ (212458343 / 1000000000) := by
  have h := checkLog_sound (w := (95703 / 904297)) (n := 12)
    (lo := (106229171 / 500000000)) (hi := (212458343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404297) = 1/(404297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-212458343 / 1000000000) (-106229171 / 500000000) (Real.log (404297 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (87700499 / 500000000) ≤ -Real.log (250000 / 297931) ∧
    -Real.log (250000 / 297931) ≤ (175400999 / 1000000000) := by
  have h := checkLog_sound (w := (47931 / 547931)) (n := 12)
    (lo := (87700499 / 500000000)) (hi := (175400999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297931 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297931 / 250000) = 1/(250000 / 297931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (87700499 / 500000000) (175400999 / 1000000000) (Real.log (297931 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (297931 / 250000) = -Real.log (250000 / 297931) := by
    rw [show ((297931 / 250000) : ℝ) = ((250000 / 297931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106425847 / 500000000) ≤ -Real.log (202069 / 250000) ∧
    -Real.log (202069 / 250000) ≤ (42570339 / 200000000) := by
  have h := checkLog_sound (w := (47931 / 452069)) (n := 12)
    (lo := (106425847 / 500000000)) (hi := (42570339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202069) = 1/(202069 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42570339 / 200000000) (-106425847 / 500000000) (Real.log (202069 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97989471 / 125000000) ≤ -Real.log (500000000000 / 1095015576323) ∧
    -Real.log (500000000000 / 1095015576323) ≤ (78391577 / 100000000) := by
  have h := checkLog_sound (w := (95015576323 / 2095015576323)) (n := 12)
    (lo := (22692147 / 250000000)) (hi := (90768589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095015576323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1095015576323 / 1000000000000) = 1/(500000000000 / 1095015576323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97989471 / 125000000) (78391577 / 100000000) (Real.log (1095015576323 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1095015576323 / 500000000000) = -Real.log (500000000000 / 1095015576323) := by
    rw [show ((1095015576323 / 500000000000) : ℝ) = ((500000000000 / 1095015576323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (196319359 / 250000000) ≤ -Real.log (500000000000 / 1096507639539) ∧
    -Real.log (500000000000 / 1096507639539) ≤ (392638719 / 500000000) := by
  have h := checkLog_sound (w := (96507639539 / 2096507639539)) (n := 12)
    (lo := (5758141 / 62500000)) (hi := (92130257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096507639539 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096507639539 / 1000000000000) = 1/(500000000000 / 1096507639539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (196319359 / 250000000) (392638719 / 500000000) (Real.log (1096507639539 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1096507639539 / 500000000000) = -Real.log (500000000000 / 1096507639539) := by
    rw [show ((1096507639539 / 500000000000) : ℝ) = ((500000000000 / 1096507639539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108766927 / 200000000) ≤ -Real.log (500000000000 / 861299878027) ∧
    -Real.log (500000000000 / 861299878027) ≤ (135958659 / 250000000) := by
  have h := checkLog_sound (w := (361299878027 / 1361299878027)) (n := 12)
    (lo := (108766927 / 200000000)) (hi := (135958659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861299878027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861299878027 / 500000000000) = 1/(500000000000 / 861299878027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108766927 / 200000000) (135958659 / 250000000) (Real.log (861299878027 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (861299878027 / 500000000000) = -Real.log (500000000000 / 861299878027) := by
    rw [show ((861299878027 / 500000000000) : ℝ) = ((500000000000 / 861299878027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (544747007 / 1000000000) ≤ -Real.log (250000000000 / 431043031023) ∧
    -Real.log (250000000000 / 431043031023) ≤ (1063959 / 1953125) := by
  have h := checkLog_sound (w := (181043031023 / 681043031023)) (n := 12)
    (lo := (544747007 / 1000000000)) (hi := (1063959 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431043031023 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431043031023 / 250000000000) = 1/(250000000000 / 431043031023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (544747007 / 1000000000) (1063959 / 1953125) (Real.log (431043031023 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (431043031023 / 250000000000) = -Real.log (250000000000 / 431043031023) := by
    rw [show ((431043031023 / 250000000000) : ℝ) = ((250000000000 / 431043031023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (24224529 / 62500000) ≤ -Real.log (500000000000 / 736714593479) ∧
    -Real.log (500000000000 / 736714593479) ≤ (77518493 / 200000000) := by
  have h := checkLog_sound (w := (236714593479 / 1236714593479)) (n := 12)
    (lo := (24224529 / 62500000)) (hi := (77518493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736714593479 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736714593479 / 500000000000) = 1/(500000000000 / 736714593479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24224529 / 62500000) (77518493 / 200000000) (Real.log (736714593479 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (736714593479 / 500000000000) = -Real.log (500000000000 / 736714593479) := by
    rw [show ((736714593479 / 500000000000) : ℝ) = ((500000000000 / 736714593479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (97063173 / 250000000) ≤ -Real.log (250000000000 / 368600577031) ∧
    -Real.log (250000000000 / 368600577031) ≤ (388252693 / 1000000000) := by
  have h := checkLog_sound (w := (118600577031 / 618600577031)) (n := 12)
    (lo := (97063173 / 250000000)) (hi := (388252693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368600577031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368600577031 / 250000000000) = 1/(250000000000 / 368600577031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (97063173 / 250000000) (388252693 / 1000000000) (Real.log (368600577031 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (368600577031 / 250000000000) = -Real.log (250000000000 / 368600577031) := by
    rw [show ((368600577031 / 250000000000) : ℝ) = ((250000000000 / 368600577031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4681337 / 125000000) ≤ -Real.log (60202619239 / 62500000000) ∧
    -Real.log (60202619239 / 62500000000) ≤ (37450697 / 1000000000) := by
  have h := checkLog_sound (w := (2297380761 / 122702619239)) (n := 12)
    (lo := (4681337 / 125000000)) (hi := (37450697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60202619239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60202619239) = 1/(60202619239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37450697 / 1000000000) (-4681337 / 125000000) (Real.log (60202619239 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37324219 / 1000000000) ≤ -Real.log (240840935791 / 250000000000) ∧
    -Real.log (240840935791 / 250000000000) ≤ (1866211 / 50000000) := by
  have h := checkLog_sound (w := (9159064209 / 490840935791)) (n := 12)
    (lo := (37324219 / 1000000000)) (hi := (1866211 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240840935791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240840935791) = 1/(240840935791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1866211 / 50000000) (-37324219 / 1000000000) (Real.log (240840935791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell210

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell211Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell211
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (317885387 / 1000000000) ≤ -Real.log (1280 / 1759) ∧
    -Real.log (1280 / 1759) ≤ (79471347 / 250000000) := by
  have h := checkLog_sound (w := (479 / 3039)) (n := 12)
    (lo := (317885387 / 1000000000)) (hi := (79471347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759 / 1280) = 1/(1280 / 1759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (317885387 / 1000000000) (79471347 / 250000000) (Real.log (1759 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1759 / 1280) = -Real.log (1280 / 1759) := by
    rw [show ((1759 / 1280) : ℝ) = ((1280 / 1759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (468754409 / 1000000000) ≤ -Real.log (801 / 1280) ∧
    -Real.log (801 / 1280) ≤ (46875441 / 100000000) := by
  have h := checkLog_sound (w := (479 / 2081)) (n := 12)
    (lo := (468754409 / 1000000000)) (hi := (46875441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 801) = 1/(801 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46875441 / 100000000) (-468754409 / 1000000000) (Real.log (801 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158729459 / 500000000) ≤ -Real.log (5120 / 7033) ∧
    -Real.log (5120 / 7033) ≤ (317458919 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 12153)) (n := 12)
    (lo := (158729459 / 500000000)) (hi := (317458919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7033 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7033 / 5120) = 1/(5120 / 7033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158729459 / 500000000) (317458919 / 1000000000) (Real.log (7033 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7033 / 5120) = -Real.log (5120 / 7033) := by
    rw [show ((7033 / 5120) : ℝ) = ((5120 / 7033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (233909259 / 500000000) ≤ -Real.log (3207 / 5120) ∧
    -Real.log (3207 / 5120) ≤ (467818519 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 8327)) (n := 12)
    (lo := (233909259 / 500000000)) (hi := (467818519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3207) = 1/(3207 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-467818519 / 1000000000) (-233909259 / 500000000) (Real.log (3207 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235728823 / 1000000000) ≤ -Real.log (1000000 / 1265831) ∧
    -Real.log (1000000 / 1265831) ≤ (29466103 / 125000000) := by
  have h := checkLog_sound (w := (265831 / 2265831)) (n := 12)
    (lo := (235728823 / 1000000000)) (hi := (29466103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265831 / 1000000) = 1/(1000000 / 1265831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235728823 / 1000000000) (29466103 / 125000000) (Real.log (1265831 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1265831 / 1000000) = -Real.log (1000000 / 1265831) := by
    rw [show ((1265831 / 1000000) : ℝ) = ((1000000 / 1265831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (309016031 / 1000000000) ≤ -Real.log (734169 / 1000000) ∧
    -Real.log (734169 / 1000000) ≤ (9656751 / 31250000) := by
  have h := checkLog_sound (w := (265831 / 1734169)) (n := 12)
    (lo := (309016031 / 1000000000)) (hi := (9656751 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734169) = 1/(734169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9656751 / 31250000) (-309016031 / 1000000000) (Real.log (734169 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47212587 / 200000000) ≤ -Real.log (500000 / 633127) ∧
    -Real.log (500000 / 633127) ≤ (29507867 / 125000000) := by
  have h := checkLog_sound (w := (133127 / 1133127)) (n := 12)
    (lo := (47212587 / 200000000)) (hi := (29507867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633127 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633127 / 500000) = 1/(500000 / 633127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47212587 / 200000000) (29507867 / 125000000) (Real.log (633127 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (633127 / 500000) = -Real.log (500000 / 633127) := by
    rw [show ((633127 / 500000) : ℝ) = ((500000 / 633127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (309592359 / 1000000000) ≤ -Real.log (366873 / 500000) ∧
    -Real.log (366873 / 500000) ≤ (7739809 / 25000000) := by
  have h := checkLog_sound (w := (133127 / 866873)) (n := 12)
    (lo := (309592359 / 1000000000)) (hi := (7739809 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 366873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 366873) = 1/(366873 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-7739809 / 25000000) (-309592359 / 1000000000) (Real.log (366873 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175400159 / 1000000000) ≤ -Real.log (1000000 / 1191723) ∧
    -Real.log (1000000 / 1191723) ≤ (1096251 / 6250000) := by
  have h := checkLog_sound (w := (191723 / 2191723)) (n := 12)
    (lo := (175400159 / 1000000000)) (hi := (1096251 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191723 / 1000000) = 1/(1000000 / 1191723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175400159 / 1000000000) (1096251 / 6250000) (Real.log (1191723 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1191723 / 1000000) = -Real.log (1000000 / 1191723) := by
    rw [show ((1191723 / 1000000) : ℝ) = ((1000000 / 1191723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212850457 / 1000000000) ≤ -Real.log (808277 / 1000000) ∧
    -Real.log (808277 / 1000000) ≤ (106425229 / 500000000) := by
  have h := checkLog_sound (w := (191723 / 1808277)) (n := 12)
    (lo := (212850457 / 1000000000)) (hi := (106425229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808277) = 1/(808277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106425229 / 500000000) (-212850457 / 1000000000) (Real.log (808277 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43916741 / 250000000) ≤ -Real.log (1000000 / 1192041) ∧
    -Real.log (1000000 / 1192041) ≤ (35133393 / 200000000) := by
  have h := checkLog_sound (w := (192041 / 2192041)) (n := 12)
    (lo := (43916741 / 250000000)) (hi := (35133393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192041 / 1000000) = 1/(1000000 / 1192041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43916741 / 250000000) (35133393 / 200000000) (Real.log (1192041 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1192041 / 1000000) = -Real.log (1000000 / 1192041) := by
    rw [show ((1192041 / 1000000) : ℝ) = ((1000000 / 1192041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53310991 / 250000000) ≤ -Real.log (807959 / 1000000) ∧
    -Real.log (807959 / 1000000) ≤ (42648793 / 200000000) := by
  have h := checkLog_sound (w := (192041 / 1807959)) (n := 12)
    (lo := (53310991 / 250000000)) (hi := (42648793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807959) = 1/(807959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42648793 / 200000000) (-53310991 / 250000000) (Real.log (807959 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (196319359 / 250000000) ≤ -Real.log (250000000000 / 548253819769) ∧
    -Real.log (250000000000 / 548253819769) ≤ (392638719 / 500000000) := by
  have h := checkLog_sound (w := (48253819769 / 1048253819769)) (n := 12)
    (lo := (5758141 / 62500000)) (hi := (92130257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548253819769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(548253819769 / 500000000000) = 1/(250000000000 / 548253819769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (196319359 / 250000000) (392638719 / 500000000) (Real.log (548253819769 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (548253819769 / 250000000000) = -Real.log (250000000000 / 548253819769) := by
    rw [show ((548253819769 / 250000000000) : ℝ) = ((250000000000 / 548253819769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (786639797 / 1000000000) ≤ -Real.log (500000000000 / 1098002496879) ∧
    -Real.log (500000000000 / 1098002496879) ≤ (786639799 / 1000000000) := by
  have h := checkLog_sound (w := (98002496879 / 2098002496879)) (n := 12)
    (lo := (93492617 / 1000000000)) (hi := (46746309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098002496879 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1098002496879 / 1000000000000) = 1/(500000000000 / 1098002496879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (786639797 / 1000000000) (786639799 / 1000000000) (Real.log (1098002496879 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1098002496879 / 500000000000) = -Real.log (500000000000 / 1098002496879) := by
    rw [show ((1098002496879 / 500000000000) : ℝ) = ((500000000000 / 1098002496879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108948971 / 200000000) ≤ -Real.log (500000000000 / 862084206769) ∧
    -Real.log (500000000000 / 862084206769) ≤ (68093107 / 125000000) := by
  have h := checkLog_sound (w := (362084206769 / 1362084206769)) (n := 12)
    (lo := (108948971 / 200000000)) (hi := (68093107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862084206769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862084206769 / 500000000000) = 1/(500000000000 / 862084206769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108948971 / 200000000) (68093107 / 125000000) (Real.log (862084206769 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (862084206769 / 500000000000) = -Real.log (500000000000 / 862084206769) := by
    rw [show ((862084206769 / 500000000000) : ℝ) = ((500000000000 / 862084206769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272827647 / 500000000) ≤ -Real.log (250000000000 / 431434719917) ∧
    -Real.log (250000000000 / 431434719917) ≤ (109131059 / 200000000) := by
  have h := checkLog_sound (w := (181434719917 / 681434719917)) (n := 12)
    (lo := (272827647 / 500000000)) (hi := (109131059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431434719917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431434719917 / 250000000000) = 1/(250000000000 / 431434719917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (272827647 / 500000000) (109131059 / 200000000) (Real.log (431434719917 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (431434719917 / 250000000000) = -Real.log (250000000000 / 431434719917) := by
    rw [show ((431434719917 / 250000000000) : ℝ) = ((250000000000 / 431434719917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (48531327 / 125000000) ≤ -Real.log (125000000000 / 184299905849) ∧
    -Real.log (125000000000 / 184299905849) ≤ (388250617 / 1000000000) := by
  have h := checkLog_sound (w := (59299905849 / 309299905849)) (n := 12)
    (lo := (48531327 / 125000000)) (hi := (388250617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184299905849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184299905849 / 125000000000) = 1/(125000000000 / 184299905849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (48531327 / 125000000) (388250617 / 1000000000) (Real.log (184299905849 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184299905849 / 125000000000) = -Real.log (125000000000 / 184299905849) := by
    rw [show ((184299905849 / 125000000000) : ℝ) = ((125000000000 / 184299905849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (24306933 / 62500000) ≤ -Real.log (500000000000 / 737686565779) ∧
    -Real.log (500000000000 / 737686565779) ≤ (388910929 / 1000000000) := by
  have h := checkLog_sound (w := (237686565779 / 1237686565779)) (n := 12)
    (lo := (24306933 / 62500000)) (hi := (388910929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737686565779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737686565779 / 500000000000) = 1/(500000000000 / 737686565779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (24306933 / 62500000) (388910929 / 1000000000) (Real.log (737686565779 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (737686565779 / 500000000000) = -Real.log (500000000000 / 737686565779) := by
    rw [show ((737686565779 / 500000000000) : ℝ) = ((500000000000 / 737686565779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37577 / 1000000) ≤ -Real.log (963120254319 / 1000000000000) ∧
    -Real.log (963120254319 / 1000000000000) ≤ (37577001 / 1000000000) := by
  have h := checkLog_sound (w := (36879745681 / 1963120254319)) (n := 12)
    (lo := (37577 / 1000000)) (hi := (37577001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963120254319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963120254319) = 1/(963120254319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37577001 / 1000000000) (-37577 / 1000000) (Real.log (963120254319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18725149 / 500000000) ≤ -Real.log (963242291271 / 1000000000000) ∧
    -Real.log (963242291271 / 1000000000000) ≤ (37450299 / 1000000000) := by
  have h := checkLog_sound (w := (36757708729 / 1963242291271)) (n := 12)
    (lo := (18725149 / 500000000)) (hi := (37450299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963242291271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963242291271) = 1/(963242291271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-37450299 / 1000000000) (-18725149 / 500000000) (Real.log (963242291271 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell211

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell212Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell212
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (12732467 / 40000000) ≤ -Real.log (5120 / 7039) ∧
    -Real.log (5120 / 7039) ≤ (79577919 / 250000000) := by
  have h := checkLog_sound (w := (1919 / 12159)) (n := 12)
    (lo := (12732467 / 40000000)) (hi := (79577919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7039 / 5120) = 1/(5120 / 7039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12732467 / 40000000) (79577919 / 250000000) (Real.log (7039 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7039 / 5120) = -Real.log (5120 / 7039) := by
    rw [show ((7039 / 5120) : ℝ) = ((5120 / 7039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (234845589 / 500000000) ≤ -Real.log (3201 / 5120) ∧
    -Real.log (3201 / 5120) ≤ (469691179 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 8321)) (n := 12)
    (lo := (234845589 / 500000000)) (hi := (469691179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3201) = 1/(3201 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-469691179 / 1000000000) (-234845589 / 500000000) (Real.log (3201 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (317885387 / 1000000000) ≤ -Real.log (1280 / 1759) ∧
    -Real.log (1280 / 1759) ≤ (79471347 / 250000000) := by
  have h := checkLog_sound (w := (479 / 3039)) (n := 12)
    (lo := (317885387 / 1000000000)) (hi := (79471347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759 / 1280) = 1/(1280 / 1759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (317885387 / 1000000000) (79471347 / 250000000) (Real.log (1759 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1759 / 1280) = -Real.log (1280 / 1759) := by
    rw [show ((1759 / 1280) : ℝ) = ((1280 / 1759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (468754409 / 1000000000) ≤ -Real.log (801 / 1280) ∧
    -Real.log (801 / 1280) ≤ (46875441 / 100000000) := by
  have h := checkLog_sound (w := (479 / 2081)) (n := 12)
    (lo := (468754409 / 1000000000)) (hi := (46875441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 801) = 1/(801 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46875441 / 100000000) (-468754409 / 1000000000) (Real.log (801 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47212429 / 200000000) ≤ -Real.log (1000000 / 1266253) ∧
    -Real.log (1000000 / 1266253) ≤ (118031073 / 500000000) := by
  have h := checkLog_sound (w := (266253 / 2266253)) (n := 12)
    (lo := (47212429 / 200000000)) (hi := (118031073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266253 / 1000000) = 1/(1000000 / 1266253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47212429 / 200000000) (118031073 / 500000000) (Real.log (1266253 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1266253 / 1000000) = -Real.log (1000000 / 1266253) := by
    rw [show ((1266253 / 1000000) : ℝ) = ((1000000 / 1266253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77397749 / 250000000) ≤ -Real.log (733747 / 1000000) ∧
    -Real.log (733747 / 1000000) ≤ (309590997 / 1000000000) := by
  have h := checkLog_sound (w := (266253 / 1733747)) (n := 12)
    (lo := (77397749 / 250000000)) (hi := (309590997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733747) = 1/(733747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-309590997 / 1000000000) (-77397749 / 250000000) (Real.log (733747 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (118198073 / 500000000) ≤ -Real.log (250000 / 316669) ∧
    -Real.log (250000 / 316669) ≤ (236396147 / 1000000000) := by
  have h := checkLog_sound (w := (66669 / 566669)) (n := 12)
    (lo := (118198073 / 500000000)) (hi := (236396147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316669 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316669 / 250000) = 1/(250000 / 316669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (118198073 / 500000000) (236396147 / 1000000000) (Real.log (316669 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (316669 / 250000) = -Real.log (250000 / 316669) := by
    rw [show ((316669 / 250000) : ℝ) = ((250000 / 316669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62033531 / 200000000) ≤ -Real.log (183331 / 250000) ∧
    -Real.log (183331 / 250000) ≤ (38770957 / 125000000) := by
  have h := checkLog_sound (w := (66669 / 433331)) (n := 12)
    (lo := (62033531 / 200000000)) (hi := (38770957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183331) = 1/(183331 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38770957 / 125000000) (-62033531 / 200000000) (Real.log (183331 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1405329 / 8000000) ≤ -Real.log (25000 / 29801) ∧
    -Real.log (25000 / 29801) ≤ (87833063 / 500000000) := by
  have h := checkLog_sound (w := (4801 / 54801)) (n := 12)
    (lo := (1405329 / 8000000)) (hi := (87833063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29801 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29801 / 25000) = 1/(25000 / 29801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1405329 / 8000000) (87833063 / 500000000) (Real.log (29801 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29801 / 25000) = -Real.log (25000 / 29801) := by
    rw [show ((29801 / 25000) : ℝ) = ((25000 / 29801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (106621363 / 500000000) ≤ -Real.log (20199 / 25000) ∧
    -Real.log (20199 / 25000) ≤ (213242727 / 1000000000) := by
  have h := checkLog_sound (w := (4801 / 45199)) (n := 12)
    (lo := (106621363 / 500000000)) (hi := (213242727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20199) = 1/(20199 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-213242727 / 1000000000) (-106621363 / 500000000) (Real.log (20199 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175932859 / 1000000000) ≤ -Real.log (500000 / 596179) ∧
    -Real.log (500000 / 596179) ≤ (8796643 / 50000000) := by
  have h := checkLog_sound (w := (96179 / 1096179)) (n := 12)
    (lo := (175932859 / 1000000000)) (hi := (8796643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596179 / 500000) = 1/(500000 / 596179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175932859 / 1000000000) (8796643 / 50000000) (Real.log (596179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (596179 / 500000) = -Real.log (500000 / 596179) := by
    rw [show ((596179 / 500000) : ℝ) = ((500000 / 596179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (213636387 / 1000000000) ≤ -Real.log (403821 / 500000) ∧
    -Real.log (403821 / 500000) ≤ (53409097 / 250000000) := by
  have h := checkLog_sound (w := (96179 / 903821)) (n := 12)
    (lo := (213636387 / 1000000000)) (hi := (53409097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403821) = 1/(403821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53409097 / 250000000) (-213636387 / 1000000000) (Real.log (403821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (786639797 / 1000000000) ≤ -Real.log (250000000000 / 549001248439) ∧
    -Real.log (250000000000 / 549001248439) ≤ (786639799 / 1000000000) := by
  have h := checkLog_sound (w := (49001248439 / 1049001248439)) (n := 12)
    (lo := (93492617 / 1000000000)) (hi := (46746309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549001248439 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(549001248439 / 500000000000) = 1/(250000000000 / 549001248439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (786639797 / 1000000000) (786639799 / 1000000000) (Real.log (549001248439 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (549001248439 / 250000000000) = -Real.log (250000000000 / 549001248439) := by
    rw [show ((549001248439 / 250000000000) : ℝ) = ((250000000000 / 549001248439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (788002853 / 1000000000) ≤ -Real.log (250000000000 / 549750078101) ∧
    -Real.log (250000000000 / 549750078101) ≤ (157600571 / 200000000) := by
  have h := checkLog_sound (w := (49750078101 / 1049750078101)) (n := 12)
    (lo := (94855673 / 1000000000)) (hi := (47427837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549750078101 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(549750078101 / 500000000000) = 1/(250000000000 / 549750078101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (788002853 / 1000000000) (157600571 / 200000000) (Real.log (549750078101 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (549750078101 / 250000000000) = -Real.log (250000000000 / 549750078101) := by
    rw [show ((549750078101 / 250000000000) : ℝ) = ((250000000000 / 549750078101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (272826571 / 500000000) ≤ -Real.log (250000000000 / 431433791211) ∧
    -Real.log (250000000000 / 431433791211) ≤ (545653143 / 1000000000) := by
  have h := checkLog_sound (w := (181433791211 / 681433791211)) (n := 12)
    (lo := (272826571 / 500000000)) (hi := (545653143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431433791211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431433791211 / 250000000000) = 1/(250000000000 / 431433791211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (272826571 / 500000000) (545653143 / 1000000000) (Real.log (431433791211 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (431433791211 / 250000000000) = -Real.log (250000000000 / 431433791211) := by
    rw [show ((431433791211 / 250000000000) : ℝ) = ((250000000000 / 431433791211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (273281901 / 500000000) ≤ -Real.log (50000000000 / 86365371923) ∧
    -Real.log (50000000000 / 86365371923) ≤ (546563803 / 1000000000) := by
  have h := checkLog_sound (w := (36365371923 / 136365371923)) (n := 12)
    (lo := (273281901 / 500000000)) (hi := (546563803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86365371923 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86365371923 / 50000000000) = 1/(50000000000 / 86365371923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (273281901 / 500000000) (546563803 / 1000000000) (Real.log (86365371923 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (86365371923 / 50000000000) = -Real.log (50000000000 / 86365371923) := by
    rw [show ((86365371923 / 50000000000) : ℝ) = ((50000000000 / 86365371923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (388908851 / 1000000000) ≤ -Real.log (62500000000 / 92210629239) ∧
    -Real.log (62500000000 / 92210629239) ≤ (97227213 / 250000000) := by
  have h := checkLog_sound (w := (29710629239 / 154710629239)) (n := 12)
    (lo := (388908851 / 1000000000)) (hi := (97227213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92210629239 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92210629239 / 62500000000) = 1/(62500000000 / 92210629239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (388908851 / 1000000000) (97227213 / 250000000) (Real.log (92210629239 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (92210629239 / 62500000000) = -Real.log (62500000000 / 92210629239) := by
    rw [show ((92210629239 / 62500000000) : ℝ) = ((62500000000 / 92210629239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (389569247 / 1000000000) ≤ -Real.log (100000000000 / 147634471709) ∧
    -Real.log (100000000000 / 147634471709) ≤ (12174039 / 31250000) := by
  have h := checkLog_sound (w := (47634471709 / 247634471709)) (n := 12)
    (lo := (389569247 / 1000000000)) (hi := (12174039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147634471709 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147634471709 / 100000000000) = 1/(100000000000 / 147634471709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (389569247 / 1000000000) (12174039 / 31250000) (Real.log (147634471709 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (147634471709 / 100000000000) = -Real.log (100000000000 / 147634471709) := by
    rw [show ((147634471709 / 100000000000) : ℝ) = ((100000000000 / 147634471709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4712941 / 125000000) ≤ -Real.log (240749599959 / 250000000000) ∧
    -Real.log (240749599959 / 250000000000) ≤ (37703529 / 1000000000) := by
  have h := checkLog_sound (w := (9250400041 / 490749599959)) (n := 12)
    (lo := (4712941 / 125000000)) (hi := (37703529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240749599959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240749599959) = 1/(240749599959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37703529 / 1000000000) (-4712941 / 125000000) (Real.log (240749599959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37576601 / 1000000000) ≤ -Real.log (601950399 / 625000000) ∧
    -Real.log (601950399 / 625000000) ≤ (18788301 / 500000000) := by
  have h := checkLog_sound (w := (23049601 / 1226950399)) (n := 12)
    (lo := (37576601 / 1000000000)) (hi := (18788301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 601950399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 601950399) = 1/(601950399 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18788301 / 500000000) (-37576601 / 1000000000) (Real.log (601950399 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell212

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (318737781 / 1000000000) ≤ -Real.log (2560 / 3521) ∧
    -Real.log (2560 / 3521) ≤ (159368891 / 500000000) := by
  have h := checkLog_sound (w := (961 / 6081)) (n := 12)
    (lo := (318737781 / 1000000000)) (hi := (159368891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3521 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3521 / 2560) = 1/(2560 / 3521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (318737781 / 1000000000) (159368891 / 500000000) (Real.log (3521 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3521 / 2560) = -Real.log (2560 / 3521) := by
    rw [show ((3521 / 2560) : ℝ) = ((2560 / 3521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58828603 / 125000000) ≤ -Real.log (1599 / 2560) ∧
    -Real.log (1599 / 2560) ≤ (18825153 / 40000000) := by
  have h := checkLog_sound (w := (961 / 4159)) (n := 12)
    (lo := (58828603 / 125000000)) (hi := (18825153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1599) = 1/(1599 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) (Real.log (1599 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12732467 / 40000000) ≤ -Real.log (5120 / 7039) ∧
    -Real.log (5120 / 7039) ≤ (79577919 / 250000000) := by
  have h := checkLog_sound (w := (1919 / 12159)) (n := 12)
    (lo := (12732467 / 40000000)) (hi := (79577919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7039 / 5120) = 1/(5120 / 7039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12732467 / 40000000) (79577919 / 250000000) (Real.log (7039 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7039 / 5120) = -Real.log (5120 / 7039) := by
    rw [show ((7039 / 5120) : ℝ) = ((5120 / 7039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (234845589 / 500000000) ≤ -Real.log (3201 / 5120) ∧
    -Real.log (3201 / 5120) ≤ (469691179 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 8321)) (n := 12)
    (lo := (234845589 / 500000000)) (hi := (469691179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3201) = 1/(3201 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-469691179 / 1000000000) (-234845589 / 500000000) (Real.log (3201 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59098839 / 250000000) ≤ -Real.log (40000 / 50667) ∧
    -Real.log (40000 / 50667) ≤ (236395357 / 1000000000) := by
  have h := checkLog_sound (w := (10667 / 90667)) (n := 12)
    (lo := (59098839 / 250000000)) (hi := (236395357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50667 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50667 / 40000) = 1/(40000 / 50667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (59098839 / 250000000) (236395357 / 1000000000) (Real.log (50667 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50667 / 40000) = -Real.log (40000 / 50667) := by
    rw [show ((50667 / 40000) : ℝ) = ((40000 / 50667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77541573 / 250000000) ≤ -Real.log (29333 / 40000) ∧
    -Real.log (29333 / 40000) ≤ (310166293 / 1000000000) := by
  have h := checkLog_sound (w := (10667 / 69333)) (n := 12)
    (lo := (77541573 / 250000000)) (hi := (310166293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29333) = 1/(29333 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-310166293 / 1000000000) (-77541573 / 250000000) (Real.log (29333 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47346007 / 200000000) ≤ -Real.log (1000000 / 1267099) ∧
    -Real.log (1000000 / 1267099) ≤ (59182509 / 250000000) := by
  have h := checkLog_sound (w := (267099 / 2267099)) (n := 12)
    (lo := (47346007 / 200000000)) (hi := (59182509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267099 / 1000000) = 1/(1000000 / 1267099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47346007 / 200000000) (59182509 / 250000000) (Real.log (1267099 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1267099 / 1000000) = -Real.log (1000000 / 1267099) := by
    rw [show ((1267099 / 1000000) : ℝ) = ((1000000 / 1267099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (310744647 / 1000000000) ≤ -Real.log (732901 / 1000000) ∧
    -Real.log (732901 / 1000000) ≤ (38843081 / 125000000) := by
  have h := checkLog_sound (w := (267099 / 1732901)) (n := 12)
    (lo := (310744647 / 1000000000)) (hi := (38843081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732901) = 1/(732901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38843081 / 125000000) (-310744647 / 1000000000) (Real.log (732901 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8796601 / 50000000) ≤ -Real.log (1000000 / 1192357) ∧
    -Real.log (1000000 / 1192357) ≤ (175932021 / 1000000000) := by
  have h := checkLog_sound (w := (192357 / 2192357)) (n := 12)
    (lo := (8796601 / 50000000)) (hi := (175932021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192357 / 1000000) = 1/(1000000 / 1192357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8796601 / 50000000) (175932021 / 1000000000) (Real.log (1192357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1192357 / 1000000) = -Real.log (1000000 / 1192357) := by
    rw [show ((1192357 / 1000000) : ℝ) = ((1000000 / 1192357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (213635149 / 1000000000) ≤ -Real.log (807643 / 1000000) ∧
    -Real.log (807643 / 1000000) ≤ (4272703 / 20000000) := by
  have h := checkLog_sound (w := (192357 / 1807643)) (n := 12)
    (lo := (213635149 / 1000000000)) (hi := (4272703 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807643) = 1/(807643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4272703 / 20000000) (-213635149 / 1000000000) (Real.log (807643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176198683 / 1000000000) ≤ -Real.log (40000 / 47707) ∧
    -Real.log (40000 / 47707) ≤ (44049671 / 250000000) := by
  have h := checkLog_sound (w := (7707 / 87707)) (n := 12)
    (lo := (176198683 / 1000000000)) (hi := (44049671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47707 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47707 / 40000) = 1/(40000 / 47707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176198683 / 1000000000) (44049671 / 250000000) (Real.log (47707 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47707 / 40000) = -Real.log (40000 / 47707) := by
    rw [show ((47707 / 40000) : ℝ) = ((40000 / 47707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42805793 / 200000000) ≤ -Real.log (32293 / 40000) ∧
    -Real.log (32293 / 40000) ≤ (107014483 / 500000000) := by
  have h := checkLog_sound (w := (7707 / 72293)) (n := 12)
    (lo := (42805793 / 200000000)) (hi := (107014483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32293) = 1/(32293 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-107014483 / 500000000) (-42805793 / 200000000) (Real.log (32293 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (788002853 / 1000000000) ≤ -Real.log (500000000000 / 1099500156201) ∧
    -Real.log (500000000000 / 1099500156201) ≤ (157600571 / 200000000) := by
  have h := checkLog_sound (w := (99500156201 / 2099500156201)) (n := 12)
    (lo := (94855673 / 1000000000)) (hi := (47427837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099500156201 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099500156201 / 1000000000000) = 1/(500000000000 / 1099500156201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (788002853 / 1000000000) (157600571 / 200000000) (Real.log (1099500156201 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1099500156201 / 500000000000) = -Real.log (500000000000 / 1099500156201) := by
    rw [show ((1099500156201 / 500000000000) : ℝ) = ((500000000000 / 1099500156201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (157873321 / 200000000) ≤ -Real.log (500000000000 / 1101000625391) ∧
    -Real.log (500000000000 / 1101000625391) ≤ (789366607 / 1000000000) := by
  have h := checkLog_sound (w := (101000625391 / 2101000625391)) (n := 12)
    (lo := (3848777 / 40000000)) (hi := (48109713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101000625391 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101000625391 / 1000000000000) = 1/(500000000000 / 1101000625391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (157873321 / 200000000) (789366607 / 1000000000) (Real.log (1101000625391 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1101000625391 / 500000000000) = -Real.log (500000000000 / 1101000625391) := by
    rw [show ((1101000625391 / 500000000000) : ℝ) = ((500000000000 / 1101000625391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (34160103 / 62500000) ≤ -Real.log (3125000000 / 5397824123) ∧
    -Real.log (3125000000 / 5397824123) ≤ (546561649 / 1000000000) := by
  have h := checkLog_sound (w := (2272824123 / 8522824123)) (n := 12)
    (lo := (34160103 / 62500000)) (hi := (546561649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5397824123 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5397824123 / 3125000000) = 1/(3125000000 / 5397824123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34160103 / 62500000) (546561649 / 1000000000) (Real.log (5397824123 / 3125000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (5397824123 / 3125000000) = -Real.log (3125000000 / 5397824123) := by
    rw [show ((5397824123 / 3125000000) : ℝ) = ((3125000000 / 5397824123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (547474683 / 1000000000) ≤ -Real.log (500000000000 / 864440763487) ∧
    -Real.log (500000000000 / 864440763487) ≤ (136868671 / 250000000) := by
  have h := checkLog_sound (w := (364440763487 / 1364440763487)) (n := 12)
    (lo := (547474683 / 1000000000)) (hi := (136868671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864440763487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864440763487 / 500000000000) = 1/(500000000000 / 864440763487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (547474683 / 1000000000) (136868671 / 250000000) (Real.log (864440763487 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (864440763487 / 500000000000) = -Real.log (500000000000 / 864440763487) := by
    rw [show ((864440763487 / 500000000000) : ℝ) = ((500000000000 / 864440763487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38956717 / 100000000) ≤ -Real.log (125000000000 / 184542706369) ∧
    -Real.log (125000000000 / 184542706369) ≤ (389567171 / 1000000000) := by
  have h := checkLog_sound (w := (59542706369 / 309542706369)) (n := 12)
    (lo := (38956717 / 100000000)) (hi := (389567171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184542706369 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184542706369 / 125000000000) = 1/(125000000000 / 184542706369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38956717 / 100000000) (389567171 / 1000000000) (Real.log (184542706369 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184542706369 / 125000000000) = -Real.log (125000000000 / 184542706369) := by
    rw [show ((184542706369 / 125000000000) : ℝ) = ((125000000000 / 184542706369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (390227649 / 1000000000) ≤ -Real.log (500000000000 / 738658532809) ∧
    -Real.log (500000000000 / 738658532809) ≤ (7804553 / 20000000) := by
  have h := checkLog_sound (w := (238658532809 / 1238658532809)) (n := 12)
    (lo := (390227649 / 1000000000)) (hi := (7804553 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738658532809 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738658532809 / 500000000000) = 1/(500000000000 / 738658532809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (390227649 / 1000000000) (7804553 / 20000000) (Real.log (738658532809 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (738658532809 / 500000000000) = -Real.log (500000000000 / 738658532809) := by
    rw [show ((738658532809 / 500000000000) : ℝ) = ((500000000000 / 738658532809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18915141 / 500000000) ≤ -Real.log (1540602151 / 1600000000) ∧
    -Real.log (1540602151 / 1600000000) ≤ (37830283 / 1000000000) := by
  have h := checkLog_sound (w := (59397849 / 3140602151)) (n := 12)
    (lo := (18915141 / 500000000)) (hi := (37830283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1540602151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1540602151) = 1/(1540602151 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37830283 / 1000000000) (-18915141 / 500000000) (Real.log (1540602151 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37703129 / 1000000000) ≤ -Real.log (962998784551 / 1000000000000) ∧
    -Real.log (962998784551 / 1000000000000) ≤ (3770313 / 100000000) := by
  have h := checkLog_sound (w := (37001215449 / 1962998784551)) (n := 12)
    (lo := (37703129 / 1000000000)) (hi := (3770313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962998784551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962998784551) = 1/(962998784551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3770313 / 100000000) (-37703129 / 1000000000) (Real.log (962998784551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (159581853 / 500000000) ≤ -Real.log (1024 / 1409) ∧
    -Real.log (1024 / 1409) ≤ (319163707 / 1000000000) := by
  have h := checkLog_sound (w := (385 / 2433)) (n := 12)
    (lo := (159581853 / 500000000)) (hi := (319163707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1024) = 1/(1024 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (159581853 / 500000000) (319163707 / 1000000000) (Real.log (1409 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1409 / 1024) = -Real.log (1024 / 1409) := by
    rw [show ((1409 / 1024) : ℝ) = ((1024 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (471567351 / 1000000000) ≤ -Real.log (639 / 1024) ∧
    -Real.log (639 / 1024) ≤ (58945919 / 125000000) := by
  have h := checkLog_sound (w := (385 / 1663)) (n := 12)
    (lo := (471567351 / 1000000000)) (hi := (58945919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 639) = 1/(639 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) (Real.log (639 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (318737781 / 1000000000) ≤ -Real.log (2560 / 3521) ∧
    -Real.log (2560 / 3521) ≤ (159368891 / 500000000) := by
  have h := checkLog_sound (w := (961 / 6081)) (n := 12)
    (lo := (318737781 / 1000000000)) (hi := (159368891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3521 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3521 / 2560) = 1/(2560 / 3521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (318737781 / 1000000000) (159368891 / 500000000) (Real.log (3521 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3521 / 2560) = -Real.log (2560 / 3521) := by
    rw [show ((3521 / 2560) : ℝ) = ((2560 / 3521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58828603 / 125000000) ≤ -Real.log (1599 / 2560) ∧
    -Real.log (1599 / 2560) ≤ (18825153 / 40000000) := by
  have h := checkLog_sound (w := (961 / 4159)) (n := 12)
    (lo := (58828603 / 125000000)) (hi := (18825153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1599) = 1/(1599 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) (Real.log (1599 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118364623 / 500000000) ≤ -Real.log (500000 / 633549) ∧
    -Real.log (500000 / 633549) ≤ (236729247 / 1000000000) := by
  have h := checkLog_sound (w := (133549 / 1133549)) (n := 12)
    (lo := (118364623 / 500000000)) (hi := (236729247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633549 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633549 / 500000) = 1/(500000 / 633549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118364623 / 500000000) (236729247 / 1000000000) (Real.log (633549 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (633549 / 500000) = -Real.log (500000 / 633549) := by
    rw [show ((633549 / 500000) : ℝ) = ((500000 / 633549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (310743283 / 1000000000) ≤ -Real.log (366451 / 500000) ∧
    -Real.log (366451 / 500000) ≤ (77685821 / 250000000) := by
  have h := checkLog_sound (w := (133549 / 866451)) (n := 12)
    (lo := (310743283 / 1000000000)) (hi := (77685821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 366451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 366451) = 1/(366451 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77685821 / 250000000) (-310743283 / 1000000000) (Real.log (366451 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (14816439 / 62500000) ≤ -Real.log (1000000 / 1267521) ∧
    -Real.log (1000000 / 1267521) ≤ (9482521 / 40000000) := by
  have h := checkLog_sound (w := (267521 / 2267521)) (n := 12)
    (lo := (14816439 / 62500000)) (hi := (9482521 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267521 / 1000000) = 1/(1000000 / 1267521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (14816439 / 62500000) (9482521 / 40000000) (Real.log (1267521 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1267521 / 1000000) = -Real.log (1000000 / 1267521) := by
    rw [show ((1267521 / 1000000) : ℝ) = ((1000000 / 1267521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (311320607 / 1000000000) ≤ -Real.log (732479 / 1000000) ∧
    -Real.log (732479 / 1000000) ≤ (9728769 / 31250000) := by
  have h := checkLog_sound (w := (267521 / 1732479)) (n := 12)
    (lo := (311320607 / 1000000000)) (hi := (9728769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732479) = 1/(732479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9728769 / 31250000) (-311320607 / 1000000000) (Real.log (732479 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35239569 / 200000000) ≤ -Real.log (500000 / 596337) ∧
    -Real.log (500000 / 596337) ≤ (88098923 / 500000000) := by
  have h := checkLog_sound (w := (96337 / 1096337)) (n := 12)
    (lo := (35239569 / 200000000)) (hi := (88098923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596337 / 500000) = 1/(500000 / 596337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35239569 / 200000000) (88098923 / 500000000) (Real.log (596337 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (596337 / 500000) = -Real.log (500000 / 596337) := by
    rw [show ((596337 / 500000) : ℝ) = ((500000 / 596337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107013863 / 500000000) ≤ -Real.log (403663 / 500000) ∧
    -Real.log (403663 / 500000) ≤ (214027727 / 1000000000) := by
  have h := checkLog_sound (w := (96337 / 903663)) (n := 12)
    (lo := (107013863 / 500000000)) (hi := (214027727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403663) = 1/(403663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214027727 / 1000000000) (-107013863 / 500000000) (Real.log (403663 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176464437 / 1000000000) ≤ -Real.log (31250 / 37281) ∧
    -Real.log (31250 / 37281) ≤ (88232219 / 500000000) := by
  have h := checkLog_sound (w := (6031 / 68531)) (n := 12)
    (lo := (176464437 / 1000000000)) (hi := (88232219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37281 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37281 / 31250) = 1/(31250 / 37281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176464437 / 1000000000) (88232219 / 500000000) (Real.log (37281 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (37281 / 31250) = -Real.log (31250 / 37281) := by
    rw [show ((37281 / 31250) : ℝ) = ((31250 / 37281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214421697 / 1000000000) ≤ -Real.log (25219 / 31250) ∧
    -Real.log (25219 / 31250) ≤ (107210849 / 500000000) := by
  have h := checkLog_sound (w := (6031 / 56469)) (n := 12)
    (lo := (214421697 / 1000000000)) (hi := (107210849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25219) = 1/(25219 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-107210849 / 500000000) (-214421697 / 1000000000) (Real.log (25219 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (157873321 / 200000000) ≤ -Real.log (50000000000 / 110100062539) ∧
    -Real.log (50000000000 / 110100062539) ≤ (789366607 / 1000000000) := by
  have h := checkLog_sound (w := (10100062539 / 210100062539)) (n := 12)
    (lo := (3848777 / 40000000)) (hi := (48109713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110100062539 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110100062539 / 100000000000) = 1/(50000000000 / 110100062539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (157873321 / 200000000) (789366607 / 1000000000) (Real.log (110100062539 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (110100062539 / 50000000000) = -Real.log (50000000000 / 110100062539) := by
    rw [show ((110100062539 / 50000000000) : ℝ) = ((50000000000 / 110100062539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49420691 / 62500000) ≤ -Real.log (125000000000 / 275625978091) ∧
    -Real.log (125000000000 / 275625978091) ≤ (395365529 / 500000000) := by
  have h := checkLog_sound (w := (25625978091 / 525625978091)) (n := 12)
    (lo := (24395969 / 250000000)) (hi := (97583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275625978091 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275625978091 / 250000000000) = 1/(125000000000 / 275625978091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (49420691 / 62500000) (395365529 / 500000000) (Real.log (275625978091 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (275625978091 / 125000000000) = -Real.log (125000000000 / 275625978091) := by
    rw [show ((275625978091 / 125000000000) : ℝ) = ((125000000000 / 275625978091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (547472529 / 1000000000) ≤ -Real.log (50000000000 / 86443890179) ∧
    -Real.log (50000000000 / 86443890179) ≤ (54747253 / 100000000) := by
  have h := checkLog_sound (w := (36443890179 / 136443890179)) (n := 12)
    (lo := (547472529 / 1000000000)) (hi := (54747253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86443890179 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86443890179 / 50000000000) = 1/(50000000000 / 86443890179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (547472529 / 1000000000) (54747253 / 100000000) (Real.log (86443890179 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (86443890179 / 50000000000) = -Real.log (50000000000 / 86443890179) := by
    rw [show ((86443890179 / 50000000000) : ℝ) = ((50000000000 / 86443890179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (548383631 / 1000000000) ≤ -Real.log (500000000000 / 865226852921) ∧
    -Real.log (500000000000 / 865226852921) ≤ (34273977 / 62500000) := by
  have h := checkLog_sound (w := (365226852921 / 1365226852921)) (n := 12)
    (lo := (548383631 / 1000000000)) (hi := (34273977 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865226852921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865226852921 / 500000000000) = 1/(500000000000 / 865226852921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (548383631 / 1000000000) (34273977 / 62500000) (Real.log (865226852921 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (865226852921 / 500000000000) = -Real.log (500000000000 / 865226852921) := by
    rw [show ((865226852921 / 500000000000) : ℝ) = ((500000000000 / 865226852921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (97556393 / 250000000) ≤ -Real.log (100000000000 / 147731399707) ∧
    -Real.log (100000000000 / 147731399707) ≤ (390225573 / 1000000000) := by
  have h := checkLog_sound (w := (47731399707 / 247731399707)) (n := 12)
    (lo := (97556393 / 250000000)) (hi := (390225573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147731399707 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147731399707 / 100000000000) = 1/(100000000000 / 147731399707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (97556393 / 250000000) (390225573 / 1000000000) (Real.log (147731399707 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (147731399707 / 100000000000) = -Real.log (100000000000 / 147731399707) := by
    rw [show ((147731399707 / 100000000000) : ℝ) = ((100000000000 / 147731399707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (195443067 / 500000000) ≤ -Real.log (500000000000 / 739145089021) ∧
    -Real.log (500000000000 / 739145089021) ≤ (78177227 / 200000000) := by
  have h := checkLog_sound (w := (239145089021 / 1239145089021)) (n := 12)
    (lo := (195443067 / 500000000)) (hi := (78177227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739145089021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739145089021 / 500000000000) = 1/(500000000000 / 739145089021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (195443067 / 500000000) (78177227 / 200000000) (Real.log (739145089021 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (739145089021 / 500000000000) = -Real.log (500000000000 / 739145089021) := by
    rw [show ((739145089021 / 500000000000) : ℝ) = ((500000000000 / 739145089021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1897863 / 50000000) ≤ -Real.log (940189539 / 976562500) ∧
    -Real.log (940189539 / 976562500) ≤ (37957261 / 1000000000) := by
  have h := checkLog_sound (w := (36372961 / 1916752039)) (n := 12)
    (lo := (1897863 / 50000000)) (hi := (37957261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 940189539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 940189539) = 1/(940189539 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37957261 / 1000000000) (-1897863 / 50000000) (Real.log (940189539 / 976562500)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37829881 / 1000000000) ≤ -Real.log (240719182431 / 250000000000) ∧
    -Real.log (240719182431 / 250000000000) ≤ (18914941 / 500000000) := by
  have h := checkLog_sound (w := (9280817569 / 490719182431)) (n := 12)
    (lo := (37829881 / 1000000000)) (hi := (18914941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240719182431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240719182431) = 1/(240719182431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18914941 / 500000000) (-37829881 / 1000000000) (Real.log (240719182431 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214

end


