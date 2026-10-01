-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0074Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0074Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:55:00.553732+00:00
-- url     : https://prove2.me/theorems/f88d5c49-bfeb-4590-b43a-12252fe09dc1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0078Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0078Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0078Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0074Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0075Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0076Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0077Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0078Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0074
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

theorem reflection_log_1_neg : (33816341 / 50000000) ≤ -Real.log (12800 / 25173) ∧
    -Real.log (12800 / 25173) ≤ (676326821 / 1000000000) := by
  have h := checkLog_sound (w := (12373 / 37973)) (n := 12)
    (lo := (33816341 / 50000000)) (hi := (676326821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25173 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25173 / 12800) = 1/(12800 / 25173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33816341 / 50000000) (676326821 / 1000000000) (Real.log (25173 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25173 / 12800) = -Real.log (12800 / 25173) := by
    rw [show ((25173 / 12800) : ℝ) = ((12800 / 25173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1700208217 / 500000000) ≤ -Real.log (427 / 12800) ∧
    -Real.log (427 / 12800) ≤ (3400416439 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 427) = 1/(427 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3400416439 / 1000000000) (-1700208217 / 500000000) (Real.log (427 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169034527 / 250000000) ≤ -Real.log (51200 / 100673) ∧
    -Real.log (51200 / 100673) ≤ (676138109 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 151873)) (n := 12)
    (lo := (169034527 / 250000000)) (hi := (676138109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100673 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100673 / 51200) = 1/(51200 / 100673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169034527 / 250000000) (676138109 / 1000000000) (Real.log (100673 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100673 / 51200) = -Real.log (51200 / 100673) := by
    rw [show ((100673 / 51200) : ℝ) = ((51200 / 100673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338935373 / 100000000) ≤ -Real.log (1727 / 51200) ∧
    -Real.log (1727 / 51200) ≤ (677870747 / 200000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1727) = 1/(1727 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-677870747 / 200000000) (-338935373 / 100000000) (Real.log (1727 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2575073 / 3906250) ≤ -Real.log (6400 / 12373) ∧
    -Real.log (6400 / 12373) ≤ (659218689 / 1000000000) := by
  have h := checkLog_sound (w := (5973 / 18773)) (n := 12)
    (lo := (2575073 / 3906250)) (hi := (659218689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12373 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12373 / 6400) = 1/(6400 / 12373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2575073 / 3906250) (659218689 / 1000000000) (Real.log (12373 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12373 / 6400) = -Real.log (6400 / 12373) := by
    rw [show ((12373 / 6400) : ℝ) = ((6400 / 12373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1353634627 / 500000000) ≤ -Real.log (427 / 6400) ∧
    -Real.log (427 / 6400) ≤ (1353634629 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 427) = 1/(427 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1353634629 / 500000000) (-1353634627 / 500000000) (Real.log (427 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (329417357 / 500000000) ≤ -Real.log (25600 / 49473) ∧
    -Real.log (25600 / 49473) ≤ (131766943 / 200000000) := by
  have h := checkLog_sound (w := (23873 / 75073)) (n := 12)
    (lo := (329417357 / 500000000)) (hi := (131766943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49473 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49473 / 25600) = 1/(25600 / 49473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (329417357 / 500000000) (131766943 / 200000000) (Real.log (49473 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49473 / 25600) = -Real.log (25600 / 49473) := by
    rw [show ((49473 / 25600) : ℝ) = ((25600 / 49473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (53924131 / 20000000) ≤ -Real.log (1727 / 25600) ∧
    -Real.log (1727 / 25600) ≤ (1348103277 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1727) = 1/(1727 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1348103277 / 500000000) (-53924131 / 20000000) (Real.log (1727 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67903 / 100000) ≤ -Real.log (250000 / 492991) ∧
    -Real.log (250000 / 492991) ≤ (679030001 / 1000000000) := by
  have h := checkLog_sound (w := (242991 / 742991)) (n := 12)
    (lo := (67903 / 100000)) (hi := (679030001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492991 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492991 / 250000) = 1/(250000 / 492991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67903 / 100000) (679030001 / 1000000000) (Real.log (492991 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (492991 / 250000) = -Real.log (250000 / 492991) := by
    rw [show ((492991 / 250000) : ℝ) = ((250000 / 492991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3574265877 / 1000000000) ≤ -Real.log (7009 / 250000) ∧
    -Real.log (7009 / 250000) ≤ (3574265883 / 1000000000) := by
  have h := checkLog_sound (w := (1607 / 29643)) (n := 12)
    (lo := (108529977 / 1000000000)) (hi := (54264989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14018) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14018) = 1/(7009 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3574265883 / 1000000000) (-3574265877 / 1000000000) (Real.log (7009 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169794643 / 250000000) ≤ -Real.log (1000000 / 1972257) ∧
    -Real.log (1000000 / 1972257) ≤ (679178573 / 1000000000) := by
  have h := checkLog_sound (w := (972257 / 2972257)) (n := 12)
    (lo := (169794643 / 250000000)) (hi := (679178573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972257 / 1000000) = 1/(1000000 / 1972257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169794643 / 250000000) (679178573 / 1000000000) (Real.log (1972257 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1972257 / 1000000) = -Real.log (1000000 / 1972257) := by
    rw [show ((1972257 / 1000000) : ℝ) = ((1000000 / 1972257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89619293 / 25000000) ≤ -Real.log (27743 / 1000000) ∧
    -Real.log (27743 / 1000000) ≤ (1792385863 / 500000000) := by
  have h := checkLog_sound (w := (3507 / 58993)) (n := 12)
    (lo := (5951791 / 50000000)) (hi := (119035821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27743) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27743) = 1/(27743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1792385863 / 500000000) (-89619293 / 25000000) (Real.log (27743 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678929587 / 1000000000) ≤ -Real.log (500000 / 985883) ∧
    -Real.log (500000 / 985883) ≤ (169732397 / 250000000) := by
  have h := checkLog_sound (w := (485883 / 1485883)) (n := 12)
    (lo := (678929587 / 1000000000)) (hi := (169732397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985883 / 500000) = 1/(500000 / 985883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678929587 / 1000000000) (169732397 / 250000000) (Real.log (985883 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (985883 / 500000) = -Real.log (500000 / 985883) := by
    rw [show ((985883 / 500000) : ℝ) = ((500000 / 985883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71344567 / 20000000) ≤ -Real.log (14117 / 500000) ∧
    -Real.log (14117 / 500000) ≤ (891807089 / 250000000) := by
  have h := checkLog_sound (w := (754 / 14871)) (n := 12)
    (lo := (2029849 / 20000000)) (hi := (101492451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14117) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14117) = 1/(14117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-891807089 / 250000000) (-71344567 / 20000000) (Real.log (14117 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679081217 / 1000000000) ≤ -Real.log (200000 / 394413) ∧
    -Real.log (200000 / 394413) ≤ (339540609 / 500000000) := by
  have h := checkLog_sound (w := (194413 / 594413)) (n := 12)
    (lo := (679081217 / 1000000000)) (hi := (339540609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394413 / 200000) = 1/(200000 / 394413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679081217 / 1000000000) (339540609 / 500000000) (Real.log (394413 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394413 / 200000) = -Real.log (200000 / 394413) := by
    rw [show ((394413 / 200000) : ℝ) = ((200000 / 394413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3577874893 / 1000000000) ≤ -Real.log (5587 / 200000) ∧
    -Real.log (5587 / 200000) ≤ (3577874899 / 1000000000) := by
  have h := checkLog_sound (w := (663 / 11837)) (n := 12)
    (lo := (112138993 / 1000000000)) (hi := (56069497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5587) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5587) = 1/(5587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3577874899 / 1000000000) (-3577874893 / 1000000000) (Real.log (5587 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4253295877 / 1000000000) ≤ -Real.log (500000000000 / 35168426309031) ∧
    -Real.log (500000000000 / 35168426309031) ≤ (1063323971 / 250000000) := by
  have h := checkLog_sound (w := (3168426309031 / 67168426309031)) (n := 12)
    (lo := (94412797 / 1000000000)) (hi := (47206399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35168426309031 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35168426309031 / 32000000000000) = 1/(500000000000 / 35168426309031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4253295877 / 1000000000) (1063323971 / 250000000) (Real.log (35168426309031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (35168426309031 / 500000000000) = -Real.log (500000000000 / 35168426309031) := by
    rw [show ((35168426309031 / 500000000000) : ℝ) = ((500000000000 / 35168426309031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4263950291 / 1000000000) ≤ -Real.log (125000000000 / 8886282125221) ∧
    -Real.log (125000000000 / 8886282125221) ≤ (2131975149 / 500000000) := by
  have h := checkLog_sound (w := (886282125221 / 16886282125221)) (n := 12)
    (lo := (105067211 / 1000000000)) (hi := (26266803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8886282125221 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8886282125221 / 8000000000000) = 1/(125000000000 / 8886282125221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4263950291 / 1000000000) (2131975149 / 500000000) (Real.log (8886282125221 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8886282125221 / 125000000000) = -Real.log (125000000000 / 8886282125221) := by
    rw [show ((8886282125221 / 125000000000) : ℝ) = ((125000000000 / 8886282125221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2123078969 / 500000000) ≤ -Real.log (250000000000 / 17459145002479) ∧
    -Real.log (250000000000 / 17459145002479) ≤ (849231589 / 200000000) := by
  have h := checkLog_sound (w := (1459145002479 / 33459145002479)) (n := 12)
    (lo := (43637429 / 500000000)) (hi := (87274859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17459145002479 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17459145002479 / 16000000000000) = 1/(250000000000 / 17459145002479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2123078969 / 500000000) (849231589 / 200000000) (Real.log (17459145002479 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17459145002479 / 250000000000) = -Real.log (250000000000 / 17459145002479) := by
    rw [show ((17459145002479 / 250000000000) : ℝ) = ((250000000000 / 17459145002479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4256956109 / 1000000000) ≤ -Real.log (100000000000 / 7059477358153) ∧
    -Real.log (100000000000 / 7059477358153) ≤ (1064239029 / 250000000) := by
  have h := checkLog_sound (w := (659477358153 / 13459477358153)) (n := 12)
    (lo := (98073029 / 1000000000)) (hi := (9807303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7059477358153 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7059477358153 / 6400000000000) = 1/(100000000000 / 7059477358153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4256956109 / 1000000000) (1064239029 / 250000000) (Real.log (7059477358153 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7059477358153 / 100000000000) = -Real.log (100000000000 / 7059477358153) := by
    rw [show ((7059477358153 / 100000000000) : ℝ) = ((100000000000 / 7059477358153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0074

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0075
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

theorem reflection_log_1_neg : (169034527 / 250000000) ≤ -Real.log (51200 / 100673) ∧
    -Real.log (51200 / 100673) ≤ (676138109 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 151873)) (n := 12)
    (lo := (169034527 / 250000000)) (hi := (676138109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100673 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100673 / 51200) = 1/(51200 / 100673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169034527 / 250000000) (676138109 / 1000000000) (Real.log (100673 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100673 / 51200) = -Real.log (51200 / 100673) := by
    rw [show ((100673 / 51200) : ℝ) = ((51200 / 100673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338935373 / 100000000) ≤ -Real.log (1727 / 51200) ∧
    -Real.log (1727 / 51200) ≤ (677870747 / 200000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1727) = 1/(1727 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-677870747 / 200000000) (-338935373 / 100000000) (Real.log (1727 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8449367 / 12500000) ≤ -Real.log (25600 / 50327) ∧
    -Real.log (25600 / 50327) ≤ (675949361 / 1000000000) := by
  have h := checkLog_sound (w := (24727 / 75927)) (n := 12)
    (lo := (8449367 / 12500000)) (hi := (675949361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50327 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50327 / 25600) = 1/(25600 / 50327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8449367 / 12500000) (675949361 / 1000000000) (Real.log (50327 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50327 / 25600) = -Real.log (25600 / 50327) := by
    rw [show ((50327 / 25600) : ℝ) = ((25600 / 50327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (422301509 / 125000000) ≤ -Real.log (873 / 25600) ∧
    -Real.log (873 / 25600) ≤ (3378412077 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 873) = 1/(873 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3378412077 / 1000000000) (-422301509 / 125000000) (Real.log (873 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (329417357 / 500000000) ≤ -Real.log (25600 / 49473) ∧
    -Real.log (25600 / 49473) ≤ (131766943 / 200000000) := by
  have h := checkLog_sound (w := (23873 / 75073)) (n := 12)
    (lo := (329417357 / 500000000)) (hi := (131766943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49473 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49473 / 25600) = 1/(25600 / 49473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (329417357 / 500000000) (131766943 / 200000000) (Real.log (49473 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49473 / 25600) = -Real.log (25600 / 49473) := by
    rw [show ((49473 / 25600) : ℝ) = ((25600 / 49473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53924131 / 20000000) ≤ -Real.log (1727 / 25600) ∧
    -Real.log (1727 / 25600) ≤ (1348103277 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1727) = 1/(1727 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1348103277 / 500000000) (-53924131 / 20000000) (Real.log (1727 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (658450593 / 1000000000) ≤ -Real.log (12800 / 24727) ∧
    -Real.log (12800 / 24727) ≤ (329225297 / 500000000) := by
  have h := checkLog_sound (w := (11927 / 37527)) (n := 12)
    (lo := (658450593 / 1000000000)) (hi := (329225297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24727 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24727 / 12800) = 1/(12800 / 24727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (658450593 / 1000000000) (329225297 / 500000000) (Real.log (24727 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24727 / 12800) = -Real.log (12800 / 24727) := by
    rw [show ((24727 / 12800) : ℝ) = ((12800 / 24727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (671316223 / 250000000) ≤ -Real.log (873 / 12800) ∧
    -Real.log (873 / 12800) ≤ (5244658 / 1953125) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 873) = 1/(873 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5244658 / 1953125) (-671316223 / 250000000) (Real.log (873 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339440703 / 500000000) ≤ -Real.log (1000000 / 1971671) ∧
    -Real.log (1000000 / 1971671) ≤ (678881407 / 1000000000) := by
  have h := checkLog_sound (w := (971671 / 2971671)) (n := 12)
    (lo := (339440703 / 500000000)) (hi := (678881407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971671 / 1000000) = 1/(1000000 / 1971671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339440703 / 500000000) (678881407 / 1000000000) (Real.log (1971671 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971671 / 1000000) = -Real.log (1000000 / 1971671) := by
    rw [show ((1971671 / 1000000) : ℝ) = ((1000000 / 1971671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3563869261 / 1000000000) ≤ -Real.log (28329 / 1000000) ∧
    -Real.log (28329 / 1000000) ≤ (3563869267 / 1000000000) := by
  have h := checkLog_sound (w := (2921 / 59579)) (n := 12)
    (lo := (98133361 / 1000000000)) (hi := (49066681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28329) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28329) = 1/(28329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3563869267 / 1000000000) (-3563869261 / 1000000000) (Real.log (28329 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (679030507 / 1000000000) ≤ -Real.log (200000 / 394393) ∧
    -Real.log (200000 / 394393) ≤ (169757627 / 250000000) := by
  have h := checkLog_sound (w := (194393 / 594393)) (n := 12)
    (lo := (679030507 / 1000000000)) (hi := (169757627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394393 / 200000) = 1/(200000 / 394393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (679030507 / 1000000000) (169757627 / 250000000) (Real.log (394393 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394393 / 200000) = -Real.log (200000 / 394393) := by
    rw [show ((394393 / 200000) : ℝ) = ((200000 / 394393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1787150773 / 500000000) ≤ -Real.log (5607 / 200000) ∧
    -Real.log (5607 / 200000) ≤ (223393847 / 62500000) := by
  have h := checkLog_sound (w := (643 / 11857)) (n := 12)
    (lo := (54282823 / 500000000)) (hi := (108565647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5607) = 1/(5607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223393847 / 62500000) (-1787150773 / 500000000) (Real.log (5607 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13575579 / 20000000) ≤ -Real.log (1000000 / 1971469) ∧
    -Real.log (1000000 / 1971469) ≤ (678778951 / 1000000000) := by
  have h := checkLog_sound (w := (971469 / 2971469)) (n := 12)
    (lo := (13575579 / 20000000)) (hi := (678778951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971469 / 1000000) = 1/(1000000 / 1971469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13575579 / 20000000) (678778951 / 1000000000) (Real.log (1971469 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1971469 / 1000000) = -Real.log (1000000 / 1971469) := by
    rw [show ((1971469 / 1000000) : ℝ) = ((1000000 / 1971469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (177838203 / 50000000) ≤ -Real.log (28531 / 1000000) ∧
    -Real.log (28531 / 1000000) ≤ (1778382033 / 500000000) := by
  have h := checkLog_sound (w := (2719 / 59781)) (n := 12)
    (lo := (284463 / 3125000)) (hi := (91028161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28531) = 1/(28531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1778382033 / 500000000) (-177838203 / 50000000) (Real.log (28531 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135786019 / 200000000) ≤ -Real.log (1000000 / 1971767) ∧
    -Real.log (1000000 / 1971767) ≤ (42433131 / 62500000) := by
  have h := checkLog_sound (w := (971767 / 2971767)) (n := 12)
    (lo := (135786019 / 200000000)) (hi := (42433131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971767 / 1000000) = 1/(1000000 / 1971767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135786019 / 200000000) (42433131 / 62500000) (Real.log (1971767 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1971767 / 1000000) = -Real.log (1000000 / 1971767) := by
    rw [show ((1971767 / 1000000) : ℝ) = ((1000000 / 1971767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3567263769 / 1000000000) ≤ -Real.log (28233 / 1000000) ∧
    -Real.log (28233 / 1000000) ≤ (142690551 / 40000000) := by
  have h := checkLog_sound (w := (3017 / 59483)) (n := 12)
    (lo := (101527869 / 1000000000)) (hi := (10152787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28233) = 1/(28233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142690551 / 40000000) (-3567263769 / 1000000000) (Real.log (28233 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4242750667 / 1000000000) ≤ -Real.log (4000000000 / 278396131173) ∧
    -Real.log (4000000000 / 278396131173) ≤ (2121375337 / 500000000) := by
  have h := checkLog_sound (w := (22396131173 / 534396131173)) (n := 12)
    (lo := (83867587 / 1000000000)) (hi := (20966897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278396131173 / 256000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(278396131173 / 256000000000) = 1/(4000000000 / 278396131173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4242750667 / 1000000000) (2121375337 / 500000000) (Real.log (278396131173 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (278396131173 / 4000000000) = -Real.log (4000000000 / 278396131173) := by
    rw [show ((278396131173 / 4000000000) : ℝ) = ((4000000000 / 278396131173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4253332053 / 1000000000) ≤ -Real.log (500000000000 / 35169698591047) ∧
    -Real.log (500000000000 / 35169698591047) ≤ (212666603 / 50000000) := by
  have h := checkLog_sound (w := (3169698591047 / 67169698591047)) (n := 12)
    (lo := (94448973 / 1000000000)) (hi := (47224487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35169698591047 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35169698591047 / 32000000000000) = 1/(500000000000 / 35169698591047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4253332053 / 1000000000) (212666603 / 50000000) (Real.log (35169698591047 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35169698591047 / 500000000000) = -Real.log (500000000000 / 35169698591047) := by
    rw [show ((35169698591047 / 500000000000) : ℝ) = ((500000000000 / 35169698591047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (423554301 / 100000000) ≤ -Real.log (20000000000 / 1381983807087) ∧
    -Real.log (20000000000 / 1381983807087) ≤ (4235543017 / 1000000000) := by
  have h := checkLog_sound (w := (101983807087 / 2661983807087)) (n := 12)
    (lo := (7665993 / 100000000)) (hi := (76659931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381983807087 / 1280000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1381983807087 / 1280000000000) = 1/(20000000000 / 1381983807087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (423554301 / 100000000) (4235543017 / 1000000000) (Real.log (1381983807087 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1381983807087 / 20000000000) = -Real.log (20000000000 / 1381983807087) := by
    rw [show ((1381983807087 / 20000000000) : ℝ) = ((20000000000 / 1381983807087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (530774233 / 125000000) ≤ -Real.log (250000000000 / 17459772252329) ∧
    -Real.log (250000000000 / 17459772252329) ≤ (4246193871 / 1000000000) := by
  have h := checkLog_sound (w := (1459772252329 / 33459772252329)) (n := 12)
    (lo := (1364231 / 15625000)) (hi := (17462157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17459772252329 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17459772252329 / 16000000000000) = 1/(250000000000 / 17459772252329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (530774233 / 125000000) (4246193871 / 1000000000) (Real.log (17459772252329 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17459772252329 / 250000000000) = -Real.log (250000000000 / 17459772252329) := by
    rw [show ((17459772252329 / 250000000000) : ℝ) = ((250000000000 / 17459772252329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0075

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0076Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0076
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

theorem reflection_log_1_neg : (8449367 / 12500000) ≤ -Real.log (25600 / 50327) ∧
    -Real.log (25600 / 50327) ≤ (675949361 / 1000000000) := by
  have h := checkLog_sound (w := (24727 / 75927)) (n := 12)
    (lo := (8449367 / 12500000)) (hi := (675949361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50327 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50327 / 25600) = 1/(25600 / 50327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8449367 / 12500000) (675949361 / 1000000000) (Real.log (50327 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50327 / 25600) = -Real.log (25600 / 50327) := by
    rw [show ((50327 / 25600) : ℝ) = ((25600 / 50327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (422301509 / 125000000) ≤ -Real.log (873 / 25600) ∧
    -Real.log (873 / 25600) ≤ (3378412077 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 873) = 1/(873 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3378412077 / 1000000000) (-422301509 / 125000000) (Real.log (873 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675760577 / 1000000000) ≤ -Real.log (10240 / 20127) ∧
    -Real.log (10240 / 20127) ≤ (337880289 / 500000000) := by
  have h := checkLog_sound (w := (9887 / 30367)) (n := 12)
    (lo := (675760577 / 1000000000)) (hi := (337880289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20127 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20127 / 10240) = 1/(10240 / 20127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675760577 / 1000000000) (337880289 / 500000000) (Real.log (20127 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20127 / 10240) = -Real.log (10240 / 20127) := by
    rw [show ((20127 / 10240) : ℝ) = ((10240 / 20127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3367588839 / 1000000000) ≤ -Real.log (353 / 10240) ∧
    -Real.log (353 / 10240) ≤ (841897211 / 250000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 353) = 1/(353 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-841897211 / 250000000) (-3367588839 / 1000000000) (Real.log (353 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (658450593 / 1000000000) ≤ -Real.log (12800 / 24727) ∧
    -Real.log (12800 / 24727) ≤ (329225297 / 500000000) := by
  have h := checkLog_sound (w := (11927 / 37527)) (n := 12)
    (lo := (658450593 / 1000000000)) (hi := (329225297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24727 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24727 / 12800) = 1/(12800 / 24727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (658450593 / 1000000000) (329225297 / 500000000) (Real.log (24727 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24727 / 12800) = -Real.log (12800 / 24727) := by
    rw [show ((24727 / 12800) : ℝ) = ((12800 / 24727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (671316223 / 250000000) ≤ -Real.log (873 / 12800) ∧
    -Real.log (873 / 12800) ≤ (5244658 / 1953125) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 873) = 1/(873 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5244658 / 1953125) (-671316223 / 250000000) (Real.log (873 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (658066323 / 1000000000) ≤ -Real.log (5120 / 9887) ∧
    -Real.log (5120 / 9887) ≤ (164516581 / 250000000) := by
  have h := checkLog_sound (w := (4767 / 15007)) (n := 12)
    (lo := (658066323 / 1000000000)) (hi := (164516581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9887 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9887 / 5120) = 1/(5120 / 9887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (658066323 / 1000000000) (164516581 / 250000000) (Real.log (9887 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9887 / 5120) = -Real.log (5120 / 9887) := by
    rw [show ((9887 / 5120) : ℝ) = ((5120 / 9887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2674441659 / 1000000000) ≤ -Real.log (353 / 5120) ∧
    -Real.log (353 / 5120) ≤ (2674441663 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 353) = 1/(353 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2674441663 / 1000000000) (-2674441659 / 1000000000) (Real.log (353 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678733297 / 1000000000) ≤ -Real.log (1000000 / 1971379) ∧
    -Real.log (1000000 / 1971379) ≤ (339366649 / 500000000) := by
  have h := checkLog_sound (w := (971379 / 2971379)) (n := 12)
    (lo := (678733297 / 1000000000)) (hi := (339366649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971379 / 1000000) = 1/(1000000 / 1971379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678733297 / 1000000000) (339366649 / 500000000) (Real.log (1971379 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971379 / 1000000) = -Real.log (1000000 / 1971379) := by
    rw [show ((1971379 / 1000000) : ℝ) = ((1000000 / 1971379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1776807281 / 500000000) ≤ -Real.log (28621 / 1000000) ∧
    -Real.log (28621 / 1000000) ≤ (444201821 / 125000000) := by
  have h := checkLog_sound (w := (2629 / 59871)) (n := 12)
    (lo := (43939331 / 500000000)) (hi := (87878663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28621) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28621) = 1/(28621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-444201821 / 125000000) (-1776807281 / 500000000) (Real.log (28621 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (678881913 / 1000000000) ≤ -Real.log (125000 / 246459) ∧
    -Real.log (125000 / 246459) ≤ (339440957 / 500000000) := by
  have h := checkLog_sound (w := (121459 / 371459)) (n := 12)
    (lo := (678881913 / 1000000000)) (hi := (339440957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246459 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246459 / 125000) = 1/(125000 / 246459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (678881913 / 1000000000) (339440957 / 500000000) (Real.log (246459 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (246459 / 125000) = -Real.log (125000 / 246459) := by
    rw [show ((246459 / 125000) : ℝ) = ((125000 / 246459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3563904561 / 1000000000) ≤ -Real.log (3541 / 125000) ∧
    -Real.log (3541 / 125000) ≤ (3563904567 / 1000000000) := by
  have h := checkLog_sound (w := (1461 / 29789)) (n := 12)
    (lo := (98168661 / 1000000000)) (hi := (49084331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14164) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14164) = 1/(3541 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3563904567 / 1000000000) (-3563904561 / 1000000000) (Real.log (3541 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (339313891 / 500000000) ≤ -Real.log (1000000 / 1971171) ∧
    -Real.log (1000000 / 1971171) ≤ (678627783 / 1000000000) := by
  have h := checkLog_sound (w := (971171 / 2971171)) (n := 12)
    (lo := (339313891 / 500000000)) (hi := (678627783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971171 / 1000000) = 1/(1000000 / 1971171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (339313891 / 500000000) (678627783 / 1000000000) (Real.log (1971171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1971171 / 1000000) = -Real.log (1000000 / 1971171) := by
    rw [show ((1971171 / 1000000) : ℝ) = ((1000000 / 1971171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3546373451 / 1000000000) ≤ -Real.log (28829 / 1000000) ∧
    -Real.log (28829 / 1000000) ≤ (3546373457 / 1000000000) := by
  have h := checkLog_sound (w := (2421 / 60079)) (n := 12)
    (lo := (80637551 / 1000000000)) (hi := (5039847 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28829) = 1/(28829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3546373457 / 1000000000) (-3546373451 / 1000000000) (Real.log (28829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678779457 / 1000000000) ≤ -Real.log (100000 / 197147) ∧
    -Real.log (100000 / 197147) ≤ (339389729 / 500000000) := by
  have h := checkLog_sound (w := (97147 / 297147)) (n := 12)
    (lo := (678779457 / 1000000000)) (hi := (339389729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197147 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197147 / 100000) = 1/(100000 / 197147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678779457 / 1000000000) (339389729 / 500000000) (Real.log (197147 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (197147 / 100000) = -Real.log (100000 / 197147) := by
    rw [show ((197147 / 100000) : ℝ) = ((100000 / 197147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (355679911 / 100000000) ≤ -Real.log (2853 / 100000) ∧
    -Real.log (2853 / 100000) ≤ (889199779 / 250000000) := by
  have h := checkLog_sound (w := (136 / 2989)) (n := 12)
    (lo := (9106321 / 100000000)) (hi := (91063211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2853) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2853) = 1/(2853 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-889199779 / 250000000) (-355679911 / 100000000) (Real.log (2853 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4232347859 / 1000000000) ≤ -Real.log (100000000000 / 6887876035079) ∧
    -Real.log (100000000000 / 6887876035079) ≤ (2116173933 / 500000000) := by
  have h := checkLog_sound (w := (487876035079 / 13287876035079)) (n := 12)
    (lo := (73464779 / 1000000000)) (hi := (3673239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6887876035079 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6887876035079 / 6400000000000) = 1/(100000000000 / 6887876035079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4232347859 / 1000000000) (2116173933 / 500000000) (Real.log (6887876035079 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6887876035079 / 100000000000) = -Real.log (100000000000 / 6887876035079) := by
    rw [show ((6887876035079 / 100000000000) : ℝ) = ((100000000000 / 6887876035079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2121393237 / 500000000) ≤ -Real.log (50000000000 / 3480076249647) ∧
    -Real.log (50000000000 / 3480076249647) ≤ (4242786481 / 1000000000) := by
  have h := checkLog_sound (w := (280076249647 / 6680076249647)) (n := 12)
    (lo := (41951697 / 500000000)) (hi := (16780679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3480076249647 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3480076249647 / 3200000000000) = 1/(50000000000 / 3480076249647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2121393237 / 500000000) (4242786481 / 1000000000) (Real.log (3480076249647 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3480076249647 / 50000000000) = -Real.log (50000000000 / 3480076249647) := by
    rw [show ((3480076249647 / 50000000000) : ℝ) = ((50000000000 / 3480076249647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4225001233 / 1000000000) ≤ -Real.log (500000000000 / 34187294044191) ∧
    -Real.log (500000000000 / 34187294044191) ≤ (105625031 / 25000000) := by
  have h := checkLog_sound (w := (2187294044191 / 66187294044191)) (n := 12)
    (lo := (66118153 / 1000000000)) (hi := (33059077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34187294044191 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34187294044191 / 32000000000000) = 1/(500000000000 / 34187294044191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4225001233 / 1000000000) (105625031 / 25000000) (Real.log (34187294044191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34187294044191 / 500000000000) = -Real.log (500000000000 / 34187294044191) := by
    rw [show ((34187294044191 / 500000000000) : ℝ) = ((500000000000 / 34187294044191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4235578567 / 1000000000) ≤ -Real.log (500000000000 / 34550823694357) ∧
    -Real.log (500000000000 / 34550823694357) ≤ (2117789287 / 500000000) := by
  have h := checkLog_sound (w := (2550823694357 / 66550823694357)) (n := 12)
    (lo := (76695487 / 1000000000)) (hi := (1198367 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34550823694357 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34550823694357 / 32000000000000) = 1/(500000000000 / 34550823694357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4235578567 / 1000000000) (2117789287 / 500000000) (Real.log (34550823694357 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (34550823694357 / 500000000000) = -Real.log (500000000000 / 34550823694357) := by
    rw [show ((34550823694357 / 500000000000) : ℝ) = ((500000000000 / 34550823694357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0076

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0077Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0077
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

theorem reflection_log_1_neg : (675760577 / 1000000000) ≤ -Real.log (10240 / 20127) ∧
    -Real.log (10240 / 20127) ≤ (337880289 / 500000000) := by
  have h := checkLog_sound (w := (9887 / 30367)) (n := 12)
    (lo := (675760577 / 1000000000)) (hi := (337880289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20127 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20127 / 10240) = 1/(10240 / 20127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675760577 / 1000000000) (337880289 / 500000000) (Real.log (20127 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20127 / 10240) = -Real.log (10240 / 20127) := by
    rw [show ((20127 / 10240) : ℝ) = ((10240 / 20127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3367588839 / 1000000000) ≤ -Real.log (353 / 10240) ∧
    -Real.log (353 / 10240) ≤ (841897211 / 250000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 353) = 1/(353 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-841897211 / 250000000) (-3367588839 / 1000000000) (Real.log (353 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337785879 / 500000000) ≤ -Real.log (6400 / 12577) ∧
    -Real.log (6400 / 12577) ≤ (675571759 / 1000000000) := by
  have h := checkLog_sound (w := (6177 / 18977)) (n := 12)
    (lo := (337785879 / 500000000)) (hi := (675571759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12577 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12577 / 6400) = 1/(6400 / 12577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337785879 / 500000000) (675571759 / 1000000000) (Real.log (12577 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12577 / 6400) = -Real.log (6400 / 12577) := by
    rw [show ((12577 / 6400) : ℝ) = ((6400 / 12577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (671376299 / 200000000) ≤ -Real.log (223 / 6400) ∧
    -Real.log (223 / 6400) ≤ (6713763 / 2000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 223) = 1/(223 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6713763 / 2000000) (-671376299 / 200000000) (Real.log (223 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (658066323 / 1000000000) ≤ -Real.log (5120 / 9887) ∧
    -Real.log (5120 / 9887) ≤ (164516581 / 250000000) := by
  have h := checkLog_sound (w := (4767 / 15007)) (n := 12)
    (lo := (658066323 / 1000000000)) (hi := (164516581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9887 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9887 / 5120) = 1/(5120 / 9887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (658066323 / 1000000000) (164516581 / 250000000) (Real.log (9887 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9887 / 5120) = -Real.log (5120 / 9887) := by
    rw [show ((9887 / 5120) : ℝ) = ((5120 / 9887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2674441659 / 1000000000) ≤ -Real.log (353 / 5120) ∧
    -Real.log (353 / 5120) ≤ (2674441663 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 353) = 1/(353 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2674441663 / 1000000000) (-2674441659 / 1000000000) (Real.log (353 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (328840953 / 500000000) ≤ -Real.log (3200 / 6177) ∧
    -Real.log (3200 / 6177) ≤ (657681907 / 1000000000) := by
  have h := checkLog_sound (w := (2977 / 9377)) (n := 12)
    (lo := (328840953 / 500000000)) (hi := (657681907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 3200) = 1/(3200 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (328840953 / 500000000) (657681907 / 1000000000) (Real.log (6177 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6177 / 3200) = -Real.log (3200 / 6177) := by
    rw [show ((6177 / 3200) : ℝ) = ((3200 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (532746863 / 200000000) ≤ -Real.log (223 / 3200) ∧
    -Real.log (223 / 3200) ≤ (2663734319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 223) = 1/(223 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2663734319 / 1000000000) (-532746863 / 200000000) (Real.log (223 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678585167 / 1000000000) ≤ -Real.log (1000000 / 1971087) ∧
    -Real.log (1000000 / 1971087) ≤ (42411573 / 62500000) := by
  have h := checkLog_sound (w := (971087 / 2971087)) (n := 12)
    (lo := (678585167 / 1000000000)) (hi := (42411573 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971087 / 1000000) = 1/(1000000 / 1971087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678585167 / 1000000000) (42411573 / 62500000) (Real.log (1971087 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971087 / 1000000) = -Real.log (1000000 / 1971087) := by
    rw [show ((1971087 / 1000000) : ℝ) = ((1000000 / 1971087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (708692791 / 200000000) ≤ -Real.log (28913 / 1000000) ∧
    -Real.log (28913 / 1000000) ≤ (3543463961 / 1000000000) := by
  have h := checkLog_sound (w := (2337 / 60163)) (n := 12)
    (lo := (15545611 / 200000000)) (hi := (9716007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28913) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28913) = 1/(28913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3543463961 / 1000000000) (-708692791 / 200000000) (Real.log (28913 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135746761 / 200000000) ≤ -Real.log (50000 / 98569) ∧
    -Real.log (50000 / 98569) ≤ (339366903 / 500000000) := by
  have h := checkLog_sound (w := (48569 / 148569)) (n := 12)
    (lo := (135746761 / 200000000)) (hi := (339366903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98569 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98569 / 50000) = 1/(50000 / 98569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135746761 / 200000000) (339366903 / 500000000) (Real.log (98569 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98569 / 50000) = -Real.log (50000 / 98569) := by
    rw [show ((98569 / 50000) : ℝ) = ((50000 / 98569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1776824751 / 500000000) ≤ -Real.log (1431 / 50000) ∧
    -Real.log (1431 / 50000) ≤ (888412377 / 250000000) := by
  have h := checkLog_sound (w := (263 / 5987)) (n := 12)
    (lo := (43956801 / 500000000)) (hi := (87913603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2862) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2862) = 1/(1431 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-888412377 / 250000000) (-1776824751 / 500000000) (Real.log (1431 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678477099 / 1000000000) ≤ -Real.log (500000 / 985437) ∧
    -Real.log (500000 / 985437) ≤ (6784771 / 10000000) := by
  have h := checkLog_sound (w := (485437 / 1485437)) (n := 12)
    (lo := (678477099 / 1000000000)) (hi := (6784771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985437 / 500000) = 1/(500000 / 985437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678477099 / 1000000000) (6784771 / 10000000) (Real.log (985437 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (985437 / 500000) = -Real.log (500000 / 985437) := by
    rw [show ((985437 / 500000) : ℝ) = ((500000 / 985437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353612403 / 100000000) ≤ -Real.log (14563 / 500000) ∧
    -Real.log (14563 / 500000) ≤ (884031009 / 250000000) := by
  have h := checkLog_sound (w := (531 / 15094)) (n := 12)
    (lo := (7038813 / 100000000)) (hi := (70388131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14563) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14563) = 1/(14563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-884031009 / 250000000) (-353612403 / 100000000) (Real.log (14563 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678628289 / 1000000000) ≤ -Real.log (250000 / 492793) ∧
    -Real.log (250000 / 492793) ≤ (67862829 / 100000000) := by
  have h := checkLog_sound (w := (242793 / 742793)) (n := 12)
    (lo := (678628289 / 1000000000)) (hi := (67862829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492793 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492793 / 250000) = 1/(250000 / 492793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678628289 / 1000000000) (67862829 / 100000000) (Real.log (492793 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (492793 / 250000) = -Real.log (250000 / 492793) := by
    rw [show ((492793 / 250000) : ℝ) = ((250000 / 492793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3546408139 / 1000000000) ≤ -Real.log (7207 / 250000) ∧
    -Real.log (7207 / 250000) ≤ (709281629 / 200000000) := by
  have h := checkLog_sound (w := (1211 / 30039)) (n := 12)
    (lo := (80672239 / 1000000000)) (hi := (1008403 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14414) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14414) = 1/(7207 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-709281629 / 200000000) (-3546408139 / 1000000000) (Real.log (7207 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4222049121 / 1000000000) ≤ -Real.log (100000000000 / 6817303635043) ∧
    -Real.log (100000000000 / 6817303635043) ≤ (527756141 / 125000000) := by
  have h := checkLog_sound (w := (417303635043 / 13217303635043)) (n := 12)
    (lo := (63166041 / 1000000000)) (hi := (31583021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817303635043 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6817303635043 / 6400000000000) = 1/(100000000000 / 6817303635043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4222049121 / 1000000000) (527756141 / 125000000) (Real.log (6817303635043 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6817303635043 / 100000000000) = -Real.log (100000000000 / 6817303635043) := by
    rw [show ((6817303635043 / 100000000000) : ℝ) = ((100000000000 / 6817303635043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2116191653 / 500000000) ≤ -Real.log (500000000000 / 34440600978337) ∧
    -Real.log (500000000000 / 34440600978337) ≤ (4232383313 / 1000000000) := by
  have h := checkLog_sound (w := (2440600978337 / 66440600978337)) (n := 12)
    (lo := (36750113 / 500000000)) (hi := (73500227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34440600978337 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34440600978337 / 32000000000000) = 1/(500000000000 / 34440600978337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2116191653 / 500000000) (4232383313 / 1000000000) (Real.log (34440600978337 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34440600978337 / 500000000000) = -Real.log (500000000000 / 34440600978337) := by
    rw [show ((34440600978337 / 500000000000) : ℝ) = ((500000000000 / 34440600978337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (526825141 / 125000000) ≤ -Real.log (500000000000 / 33833585112957) ∧
    -Real.log (500000000000 / 33833585112957) ≤ (842920227 / 200000000) := by
  have h := checkLog_sound (w := (1833585112957 / 65833585112957)) (n := 12)
    (lo := (1741189 / 31250000)) (hi := (55718049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33833585112957 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33833585112957 / 32000000000000) = 1/(500000000000 / 33833585112957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (526825141 / 125000000) (842920227 / 200000000) (Real.log (33833585112957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (33833585112957 / 500000000000) = -Real.log (500000000000 / 33833585112957) := by
    rw [show ((33833585112957 / 500000000000) : ℝ) = ((500000000000 / 33833585112957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1056259107 / 250000000) ≤ -Real.log (250000000000 / 17094248647149) ∧
    -Real.log (250000000000 / 17094248647149) ≤ (845007287 / 200000000) := by
  have h := checkLog_sound (w := (1094248647149 / 33094248647149)) (n := 12)
    (lo := (16538337 / 250000000)) (hi := (66153349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17094248647149 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17094248647149 / 16000000000000) = 1/(250000000000 / 17094248647149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1056259107 / 250000000) (845007287 / 200000000) (Real.log (17094248647149 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17094248647149 / 250000000000) = -Real.log (250000000000 / 17094248647149) := by
    rw [show ((17094248647149 / 250000000000) : ℝ) = ((250000000000 / 17094248647149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0077

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0078Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0078
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

theorem reflection_log_1_neg : (337785879 / 500000000) ≤ -Real.log (6400 / 12577) ∧
    -Real.log (6400 / 12577) ≤ (675571759 / 1000000000) := by
  have h := checkLog_sound (w := (6177 / 18977)) (n := 12)
    (lo := (337785879 / 500000000)) (hi := (675571759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12577 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12577 / 6400) = 1/(6400 / 12577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337785879 / 500000000) (675571759 / 1000000000) (Real.log (12577 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12577 / 6400) = -Real.log (6400 / 12577) := by
    rw [show ((12577 / 6400) : ℝ) = ((6400 / 12577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (671376299 / 200000000) ≤ -Real.log (223 / 6400) ∧
    -Real.log (223 / 6400) ≤ (6713763 / 2000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 223) = 1/(223 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6713763 / 2000000) (-671376299 / 200000000) (Real.log (223 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84422863 / 125000000) ≤ -Real.log (51200 / 100597) ∧
    -Real.log (51200 / 100597) ≤ (135076581 / 200000000) := by
  have h := checkLog_sound (w := (49397 / 151797)) (n := 12)
    (lo := (84422863 / 125000000)) (hi := (135076581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100597 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100597 / 51200) = 1/(51200 / 100597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84422863 / 125000000) (135076581 / 200000000) (Real.log (100597 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100597 / 51200) = -Real.log (51200 / 100597) := by
    rw [show ((100597 / 51200) : ℝ) = ((51200 / 100597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (669257517 / 200000000) ≤ -Real.log (1803 / 51200) ∧
    -Real.log (1803 / 51200) ≤ (334628759 / 100000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1803) = 1/(1803 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334628759 / 100000000) (-669257517 / 200000000) (Real.log (1803 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (328840953 / 500000000) ≤ -Real.log (3200 / 6177) ∧
    -Real.log (3200 / 6177) ≤ (657681907 / 1000000000) := by
  have h := checkLog_sound (w := (2977 / 9377)) (n := 12)
    (lo := (328840953 / 500000000)) (hi := (657681907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 3200) = 1/(3200 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (328840953 / 500000000) (657681907 / 1000000000) (Real.log (6177 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6177 / 3200) = -Real.log (3200 / 6177) := by
    rw [show ((6177 / 3200) : ℝ) = ((3200 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (532746863 / 200000000) ≤ -Real.log (223 / 3200) ∧
    -Real.log (223 / 3200) ≤ (2663734319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 223) = 1/(223 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2663734319 / 1000000000) (-532746863 / 200000000) (Real.log (223 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (328648671 / 500000000) ≤ -Real.log (25600 / 49397) ∧
    -Real.log (25600 / 49397) ≤ (657297343 / 1000000000) := by
  have h := checkLog_sound (w := (23797 / 74997)) (n := 12)
    (lo := (328648671 / 500000000)) (hi := (657297343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49397 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49397 / 25600) = 1/(25600 / 49397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (328648671 / 500000000) (657297343 / 1000000000) (Real.log (49397 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49397 / 25600) = -Real.log (25600 / 49397) := by
    rw [show ((49397 / 25600) : ℝ) = ((25600 / 49397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (530628081 / 200000000) ≤ -Real.log (1803 / 25600) ∧
    -Real.log (1803 / 25600) ≤ (2653140409 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1803) = 1/(1803 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2653140409 / 1000000000) (-530628081 / 200000000) (Real.log (1803 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339218507 / 500000000) ≤ -Real.log (200000 / 394159) ∧
    -Real.log (200000 / 394159) ≤ (135687403 / 200000000) := by
  have h := checkLog_sound (w := (194159 / 594159)) (n := 12)
    (lo := (339218507 / 500000000)) (hi := (135687403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394159 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394159 / 200000) = 1/(200000 / 394159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339218507 / 500000000) (135687403 / 200000000) (Real.log (394159 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (394159 / 200000) = -Real.log (200000 / 394159) := by
    rw [show ((394159 / 200000) : ℝ) = ((200000 / 394159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (883353837 / 250000000) ≤ -Real.log (5841 / 200000) ∧
    -Real.log (5841 / 200000) ≤ (1766707677 / 500000000) := by
  have h := checkLog_sound (w := (409 / 12091)) (n := 12)
    (lo := (8459931 / 125000000)) (hi := (67679449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5841) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5841) = 1/(5841 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1766707677 / 500000000) (-883353837 / 250000000) (Real.log (5841 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339292837 / 500000000) ≤ -Real.log (62500 / 123193) ∧
    -Real.log (62500 / 123193) ≤ (27143427 / 40000000) := by
  have h := checkLog_sound (w := (60693 / 185693)) (n := 12)
    (lo := (339292837 / 500000000)) (hi := (27143427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123193 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123193 / 62500) = 1/(62500 / 123193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339292837 / 500000000) (27143427 / 40000000) (Real.log (123193 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (123193 / 62500) = -Real.log (62500 / 123193) := by
    rw [show ((123193 / 62500) : ℝ) = ((62500 / 123193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1771749271 / 500000000) ≤ -Real.log (1807 / 62500) ∧
    -Real.log (1807 / 62500) ≤ (885874637 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 30081)) (n := 12)
    (lo := (38881321 / 500000000)) (hi := (77762643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14456) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14456) = 1/(1807 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-885874637 / 250000000) (-1771749271 / 500000000) (Real.log (1807 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678326393 / 1000000000) ≤ -Real.log (1000000 / 1970577) ∧
    -Real.log (1000000 / 1970577) ≤ (339163197 / 500000000) := by
  have h := checkLog_sound (w := (970577 / 2970577)) (n := 12)
    (lo := (678326393 / 1000000000)) (hi := (339163197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970577 / 1000000) = 1/(1000000 / 1970577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678326393 / 1000000000) (339163197 / 500000000) (Real.log (1970577 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1970577 / 1000000) = -Real.log (1000000 / 1970577) := by
    rw [show ((1970577 / 1000000) : ℝ) = ((1000000 / 1970577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1762989297 / 500000000) ≤ -Real.log (29423 / 1000000) ∧
    -Real.log (29423 / 1000000) ≤ (17629893 / 5000000) := by
  have h := checkLog_sound (w := (1827 / 60673)) (n := 12)
    (lo := (30121347 / 500000000)) (hi := (12048539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29423) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29423) = 1/(29423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-17629893 / 5000000) (-1762989297 / 500000000) (Real.log (29423 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (339238803 / 500000000) ≤ -Real.log (8000 / 15767) ∧
    -Real.log (8000 / 15767) ≤ (678477607 / 1000000000) := by
  have h := checkLog_sound (w := (7767 / 23767)) (n := 12)
    (lo := (339238803 / 500000000)) (hi := (678477607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15767 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15767 / 8000) = 1/(8000 / 15767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (339238803 / 500000000) (678477607 / 1000000000) (Real.log (15767 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15767 / 8000) = -Real.log (8000 / 15767) := by
    rw [show ((15767 / 8000) : ℝ) = ((8000 / 15767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (884039591 / 250000000) ≤ -Real.log (233 / 8000) ∧
    -Real.log (233 / 8000) ≤ (353615837 / 100000000) := by
  have h := checkLog_sound (w := (17 / 483)) (n := 12)
    (lo := (1100351 / 15625000)) (hi := (14084493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(250 / 233) = 1/(233 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-353615837 / 100000000) (-884039591 / 250000000) (Real.log (233 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2105926181 / 500000000) ≤ -Real.log (500000000000 / 33740712206813) ∧
    -Real.log (500000000000 / 33740712206813) ≤ (4211852369 / 1000000000) := by
  have h := checkLog_sound (w := (1740712206813 / 65740712206813)) (n := 12)
    (lo := (26484641 / 500000000)) (hi := (52969283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33740712206813 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33740712206813 / 32000000000000) = 1/(500000000000 / 33740712206813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2105926181 / 500000000) (4211852369 / 1000000000) (Real.log (33740712206813 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (33740712206813 / 500000000000) = -Real.log (500000000000 / 33740712206813) := by
    rw [show ((33740712206813 / 500000000000) : ℝ) = ((500000000000 / 33740712206813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (527760527 / 125000000) ≤ -Real.log (50000000000 / 3408771444383) ∧
    -Real.log (50000000000 / 3408771444383) ≤ (4222084223 / 1000000000) := by
  have h := checkLog_sound (w := (208771444383 / 6608771444383)) (n := 12)
    (lo := (3950071 / 62500000)) (hi := (63201137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3408771444383 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3408771444383 / 3200000000000) = 1/(50000000000 / 3408771444383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (527760527 / 125000000) (4222084223 / 1000000000) (Real.log (3408771444383 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3408771444383 / 50000000000) = -Real.log (50000000000 / 3408771444383) := by
    rw [show ((3408771444383 / 50000000000) : ℝ) = ((50000000000 / 3408771444383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4204304987 / 1000000000) ≤ -Real.log (500000000000 / 33487016959521) ∧
    -Real.log (500000000000 / 33487016959521) ≤ (2102152497 / 500000000) := by
  have h := checkLog_sound (w := (1487016959521 / 65487016959521)) (n := 12)
    (lo := (45421907 / 1000000000)) (hi := (11355477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33487016959521 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33487016959521 / 32000000000000) = 1/(500000000000 / 33487016959521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4204304987 / 1000000000) (2102152497 / 500000000) (Real.log (33487016959521 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (33487016959521 / 500000000000) = -Real.log (500000000000 / 33487016959521) := by
    rw [show ((33487016959521 / 500000000000) : ℝ) = ((500000000000 / 33487016959521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421463597 / 100000000) ≤ -Real.log (250000000000 / 16917381974249) ∧
    -Real.log (250000000000 / 16917381974249) ≤ (4214635977 / 1000000000) := by
  have h := checkLog_sound (w := (917381974249 / 32917381974249)) (n := 12)
    (lo := (5575289 / 100000000)) (hi := (55752891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16917381974249 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16917381974249 / 16000000000000) = 1/(250000000000 / 16917381974249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421463597 / 100000000) (4214635977 / 1000000000) (Real.log (16917381974249 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16917381974249 / 250000000000) = -Real.log (250000000000 / 16917381974249) := by
    rw [show ((16917381974249 / 250000000000) : ℝ) = ((250000000000 / 16917381974249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0078

end


