-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0056Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0056Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:55:00.291982+00:00
-- url     : https://prove2.me/theorems/b9458e6d-c938-4b67-b0e5-2aa35f4d459b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0059Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0059Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0059Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0056Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0057Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0058Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0059Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056
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

theorem reflection_log_1_neg : (678494453 / 1000000000) ≤ -Real.log (102400 / 201821) ∧
    -Real.log (102400 / 201821) ≤ (339247227 / 500000000) := by
  have h := checkLog_sound (w := (99421 / 304221)) (n := 12)
    (lo := (678494453 / 1000000000)) (hi := (339247227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201821 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201821 / 102400) = 1/(102400 / 201821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678494453 / 1000000000) (339247227 / 500000000) (Real.log (201821 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201821 / 102400) = -Real.log (102400 / 201821) := by
    rw [show ((201821 / 102400) : ℝ) = ((102400 / 201821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (884324759 / 250000000) ≤ -Real.log (2979 / 102400) ∧
    -Real.log (2979 / 102400) ≤ (1768649521 / 500000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2979) = 1/(2979 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1768649521 / 500000000) (-884324759 / 250000000) (Real.log (2979 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339200153 / 500000000) ≤ -Real.log (51200 / 100901) ∧
    -Real.log (51200 / 100901) ≤ (678400307 / 1000000000) := by
  have h := checkLog_sound (w := (49701 / 152101)) (n := 12)
    (lo := (339200153 / 500000000)) (hi := (678400307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100901 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100901 / 51200) = 1/(51200 / 100901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339200153 / 500000000) (678400307 / 1000000000) (Real.log (100901 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100901 / 51200) = -Real.log (51200 / 100901) := by
    rw [show ((100901 / 51200) : ℝ) = ((51200 / 100901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (353094131 / 100000000) ≤ -Real.log (1499 / 51200) ∧
    -Real.log (1499 / 51200) ≤ (882735329 / 250000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1499) = 1/(1499 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-882735329 / 250000000) (-353094131 / 100000000) (Real.log (1499 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331811913 / 500000000) ≤ -Real.log (51200 / 99421) ∧
    -Real.log (51200 / 99421) ≤ (663623827 / 1000000000) := by
  have h := checkLog_sound (w := (48221 / 150621)) (n := 12)
    (lo := (331811913 / 500000000)) (hi := (663623827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99421 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99421 / 51200) = 1/(51200 / 99421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (331811913 / 500000000) (663623827 / 1000000000) (Real.log (99421 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99421 / 51200) = -Real.log (51200 / 99421) := by
    rw [show ((99421 / 51200) : ℝ) = ((51200 / 99421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (177759491 / 62500000) ≤ -Real.log (2979 / 51200) ∧
    -Real.log (2979 / 51200) ≤ (2844151861 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2979) = 1/(2979 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2844151861 / 1000000000) (-177759491 / 62500000) (Real.log (2979 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331716351 / 500000000) ≤ -Real.log (25600 / 49701) ∧
    -Real.log (25600 / 49701) ≤ (663432703 / 1000000000) := by
  have h := checkLog_sound (w := (24101 / 75301)) (n := 12)
    (lo := (331716351 / 500000000)) (hi := (663432703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49701 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49701 / 25600) = 1/(25600 / 49701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331716351 / 500000000) (663432703 / 1000000000) (Real.log (49701 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49701 / 25600) = -Real.log (25600 / 49701) := by
    rw [show ((49701 / 25600) : ℝ) = ((25600 / 49701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283779413 / 100000000) ≤ -Real.log (1499 / 25600) ∧
    -Real.log (1499 / 25600) ≤ (567558827 / 200000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1499) = 1/(1499 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567558827 / 200000000) (-283779413 / 100000000) (Real.log (1499 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340409753 / 500000000) ≤ -Real.log (125000 / 246937) ∧
    -Real.log (125000 / 246937) ≤ (680819507 / 1000000000) := by
  have h := checkLog_sound (w := (121937 / 371937)) (n := 12)
    (lo := (340409753 / 500000000)) (hi := (680819507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246937 / 125000) = 1/(125000 / 246937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340409753 / 500000000) (680819507 / 1000000000) (Real.log (246937 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (246937 / 125000) = -Real.log (125000 / 246937) := by
    rw [show ((246937 / 125000) : ℝ) = ((125000 / 246937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1854459453 / 500000000) ≤ -Real.log (3063 / 125000) ∧
    -Real.log (3063 / 125000) ≤ (28975929 / 7812500) := by
  have h := checkLog_sound (w := (3373 / 27877)) (n := 12)
    (lo := (121591503 / 500000000)) (hi := (243183007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12252) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12252) = 1/(3063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28975929 / 7812500) (-1854459453 / 500000000) (Real.log (3063 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680894927 / 1000000000) ≤ -Real.log (200000 / 395129) ∧
    -Real.log (200000 / 395129) ≤ (42555933 / 62500000) := by
  have h := checkLog_sound (w := (195129 / 595129)) (n := 12)
    (lo := (680894927 / 1000000000)) (hi := (42555933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395129 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395129 / 200000) = 1/(200000 / 395129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680894927 / 1000000000) (42555933 / 62500000) (Real.log (395129 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (395129 / 200000) = -Real.log (200000 / 395129) := by
    rw [show ((395129 / 200000) : ℝ) = ((200000 / 395129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (928754527 / 250000000) ≤ -Real.log (4871 / 200000) ∧
    -Real.log (4871 / 200000) ≤ (1857509057 / 500000000) := by
  have h := checkLog_sound (w := (1379 / 11121)) (n := 12)
    (lo := (7790069 / 31250000)) (hi := (249282209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4871) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4871) = 1/(4871 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1857509057 / 500000000) (-928754527 / 250000000) (Real.log (4871 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68074661 / 100000000) ≤ -Real.log (125000 / 246919) ∧
    -Real.log (125000 / 246919) ≤ (680746611 / 1000000000) := by
  have h := checkLog_sound (w := (121919 / 371919)) (n := 12)
    (lo := (68074661 / 100000000)) (hi := (680746611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246919 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246919 / 125000) = 1/(125000 / 246919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68074661 / 100000000) (680746611 / 1000000000) (Real.log (246919 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246919 / 125000) = -Real.log (125000 / 246919) := by
    rw [show ((246919 / 125000) : ℝ) = ((125000 / 246919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1851529757 / 500000000) ≤ -Real.log (3081 / 125000) ∧
    -Real.log (3081 / 125000) ≤ (11572061 / 3125000) := by
  have h := checkLog_sound (w := (3301 / 27949)) (n := 12)
    (lo := (118661807 / 500000000)) (hi := (47464723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12324) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12324) = 1/(3081 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11572061 / 3125000) (-1851529757 / 500000000) (Real.log (3081 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680823049 / 1000000000) ≤ -Real.log (1000000 / 1975503) ∧
    -Real.log (1000000 / 1975503) ≤ (13616461 / 20000000) := by
  have h := checkLog_sound (w := (975503 / 2975503)) (n := 12)
    (lo := (680823049 / 1000000000)) (hi := (13616461 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975503 / 1000000) = 1/(1000000 / 1975503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680823049 / 1000000000) (13616461 / 20000000) (Real.log (1975503 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975503 / 1000000) = -Real.log (1000000 / 1975503) := by
    rw [show ((1975503 / 1000000) : ℝ) = ((1000000 / 1975503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (741840923 / 200000000) ≤ -Real.log (24497 / 1000000) ∧
    -Real.log (24497 / 1000000) ≤ (3709204621 / 1000000000) := by
  have h := checkLog_sound (w := (6753 / 55747)) (n := 12)
    (lo := (48693743 / 200000000)) (hi := (60867179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24497) = 1/(24497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3709204621 / 1000000000) (-741840923 / 200000000) (Real.log (24497 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1097434603 / 250000000) ≤ -Real.log (50000000000 / 4030966372837) ∧
    -Real.log (50000000000 / 4030966372837) ≤ (4389738419 / 1000000000) := by
  have h := checkLog_sound (w := (830966372837 / 7230966372837)) (n := 12)
    (lo := (57713833 / 250000000)) (hi := (230855333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4030966372837 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4030966372837 / 3200000000000) = 1/(50000000000 / 4030966372837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1097434603 / 250000000) (4389738419 / 1000000000) (Real.log (4030966372837 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4030966372837 / 50000000000) = -Real.log (50000000000 / 4030966372837) := by
    rw [show ((4030966372837 / 50000000000) : ℝ) = ((50000000000 / 4030966372837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (879182607 / 200000000) ≤ -Real.log (50000000000 / 4055933073291) ∧
    -Real.log (50000000000 / 4055933073291) ≤ (2197956521 / 500000000) := by
  have h := checkLog_sound (w := (855933073291 / 7255933073291)) (n := 12)
    (lo := (47405991 / 200000000)) (hi := (59257489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4055933073291 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4055933073291 / 3200000000000) = 1/(50000000000 / 4055933073291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (879182607 / 200000000) (2197956521 / 500000000) (Real.log (4055933073291 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4055933073291 / 50000000000) = -Real.log (50000000000 / 4055933073291) := by
    rw [show ((4055933073291 / 50000000000) : ℝ) = ((50000000000 / 4055933073291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1095951531 / 250000000) ≤ -Real.log (62500000000 / 5008905387861) ∧
    -Real.log (62500000000 / 5008905387861) ≤ (4383806131 / 1000000000) := by
  have h := checkLog_sound (w := (1008905387861 / 9008905387861)) (n := 12)
    (lo := (56230761 / 250000000)) (hi := (44984609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5008905387861 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5008905387861 / 4000000000000) = 1/(62500000000 / 5008905387861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1095951531 / 250000000) (4383806131 / 1000000000) (Real.log (5008905387861 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5008905387861 / 62500000000) = -Real.log (62500000000 / 5008905387861) := by
    rw [show ((5008905387861 / 62500000000) : ℝ) = ((62500000000 / 5008905387861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274376729 / 62500000) ≤ -Real.log (125000000000 / 10080331265053) ∧
    -Real.log (125000000000 / 10080331265053) ≤ (4390027671 / 1000000000) := by
  have h := checkLog_sound (w := (2080331265053 / 18080331265053)) (n := 12)
    (lo := (28893073 / 125000000)) (hi := (46228917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10080331265053 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10080331265053 / 8000000000000) = 1/(125000000000 / 10080331265053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274376729 / 62500000) (4390027671 / 1000000000) (Real.log (10080331265053 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10080331265053 / 125000000000) = -Real.log (125000000000 / 10080331265053) := by
    rw [show ((10080331265053 / 125000000000) : ℝ) = ((125000000000 / 10080331265053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057
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

theorem reflection_log_1_neg : (339200153 / 500000000) ≤ -Real.log (51200 / 100901) ∧
    -Real.log (51200 / 100901) ≤ (678400307 / 1000000000) := by
  have h := checkLog_sound (w := (49701 / 152101)) (n := 12)
    (lo := (339200153 / 500000000)) (hi := (678400307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100901 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100901 / 51200) = 1/(51200 / 100901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (339200153 / 500000000) (678400307 / 1000000000) (Real.log (100901 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100901 / 51200) = -Real.log (51200 / 100901) := by
    rw [show ((100901 / 51200) : ℝ) = ((51200 / 100901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (353094131 / 100000000) ≤ -Real.log (1499 / 51200) ∧
    -Real.log (1499 / 51200) ≤ (882735329 / 250000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1499) = 1/(1499 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-882735329 / 250000000) (-353094131 / 100000000) (Real.log (1499 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678306149 / 1000000000) ≤ -Real.log (102400 / 201783) ∧
    -Real.log (102400 / 201783) ≤ (13566123 / 20000000) := by
  have h := checkLog_sound (w := (99383 / 304183)) (n := 12)
    (lo := (678306149 / 1000000000)) (hi := (13566123 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201783 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201783 / 102400) = 1/(102400 / 201783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678306149 / 1000000000) (13566123 / 20000000) (Real.log (201783 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201783 / 102400) = -Real.log (102400 / 201783) := by
    rw [show ((201783 / 102400) : ℝ) = ((102400 / 201783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3524623749 / 1000000000) ≤ -Real.log (3017 / 102400) ∧
    -Real.log (3017 / 102400) ≤ (704924751 / 200000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3017) = 1/(3017 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-704924751 / 200000000) (-3524623749 / 1000000000) (Real.log (3017 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331716351 / 500000000) ≤ -Real.log (25600 / 49701) ∧
    -Real.log (25600 / 49701) ≤ (663432703 / 1000000000) := by
  have h := checkLog_sound (w := (24101 / 75301)) (n := 12)
    (lo := (331716351 / 500000000)) (hi := (663432703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49701 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49701 / 25600) = 1/(25600 / 49701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (331716351 / 500000000) (663432703 / 1000000000) (Real.log (49701 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49701 / 25600) = -Real.log (25600 / 49701) := by
    rw [show ((49701 / 25600) : ℝ) = ((25600 / 49701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283779413 / 100000000) ≤ -Real.log (1499 / 25600) ∧
    -Real.log (1499 / 25600) ≤ (567558827 / 200000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1499) = 1/(1499 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-567558827 / 200000000) (-283779413 / 100000000) (Real.log (1499 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33162077 / 50000000) ≤ -Real.log (51200 / 99383) ∧
    -Real.log (51200 / 99383) ≤ (663241541 / 1000000000) := by
  have h := checkLog_sound (w := (48183 / 150583)) (n := 12)
    (lo := (33162077 / 50000000)) (hi := (663241541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99383 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99383 / 51200) = 1/(51200 / 99383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33162077 / 50000000) (663241541 / 1000000000) (Real.log (99383 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99383 / 51200) = -Real.log (51200 / 99383) := by
    rw [show ((99383 / 51200) : ℝ) = ((51200 / 99383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2831476569 / 1000000000) ≤ -Real.log (3017 / 51200) ∧
    -Real.log (3017 / 51200) ≤ (1415738287 / 500000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3017) = 1/(3017 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1415738287 / 500000000) (-2831476569 / 1000000000) (Real.log (3017 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136148917 / 200000000) ≤ -Real.log (250000 / 493837) ∧
    -Real.log (250000 / 493837) ≤ (340372293 / 500000000) := by
  have h := checkLog_sound (w := (243837 / 743837)) (n := 12)
    (lo := (136148917 / 200000000)) (hi := (340372293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493837 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493837 / 250000) = 1/(250000 / 493837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136148917 / 200000000) (340372293 / 500000000) (Real.log (493837 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493837 / 250000) = -Real.log (250000 / 493837) := by
    rw [show ((493837 / 250000) : ℝ) = ((250000 / 493837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3702897243 / 1000000000) ≤ -Real.log (6163 / 250000) ∧
    -Real.log (6163 / 250000) ≤ (3702897249 / 1000000000) := by
  have h := checkLog_sound (w := (3299 / 27951)) (n := 12)
    (lo := (237161343 / 1000000000)) (hi := (1852823 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12326) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12326) = 1/(6163 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3702897249 / 1000000000) (-3702897243 / 1000000000) (Real.log (6163 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170205003 / 250000000) ≤ -Real.log (1000000 / 1975497) ∧
    -Real.log (1000000 / 1975497) ≤ (680820013 / 1000000000) := by
  have h := checkLog_sound (w := (975497 / 2975497)) (n := 12)
    (lo := (170205003 / 250000000)) (hi := (680820013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975497 / 1000000) = 1/(1000000 / 1975497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170205003 / 250000000) (680820013 / 1000000000) (Real.log (1975497 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975497 / 1000000) = -Real.log (1000000 / 1975497) := by
    rw [show ((1975497 / 1000000) : ℝ) = ((1000000 / 1975497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3708959717 / 1000000000) ≤ -Real.log (24503 / 1000000) ∧
    -Real.log (24503 / 1000000) ≤ (3708959723 / 1000000000) := by
  have h := checkLog_sound (w := (6747 / 55753)) (n := 12)
    (lo := (243223817 / 1000000000)) (hi := (121611909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24503) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24503) = 1/(24503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3708959723 / 1000000000) (-3708959717 / 1000000000) (Real.log (24503 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680670671 / 1000000000) ≤ -Real.log (500000 / 987601) ∧
    -Real.log (500000 / 987601) ≤ (42541917 / 62500000) := by
  have h := checkLog_sound (w := (487601 / 1487601)) (n := 12)
    (lo := (680670671 / 1000000000)) (hi := (42541917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987601 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987601 / 500000) = 1/(500000 / 987601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680670671 / 1000000000) (42541917 / 62500000) (Real.log (987601 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987601 / 500000) = -Real.log (500000 / 987601) := by
    rw [show ((987601 / 500000) : ℝ) = ((500000 / 987601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3696992271 / 1000000000) ≤ -Real.log (12399 / 500000) ∧
    -Real.log (12399 / 500000) ≤ (3696992277 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 14012)) (n := 12)
    (lo := (231256371 / 1000000000)) (hi := (57814093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12399) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12399) = 1/(12399 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3696992277 / 1000000000) (-3696992271 / 1000000000) (Real.log (12399 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170186779 / 250000000) ≤ -Real.log (1000000 / 1975353) ∧
    -Real.log (1000000 / 1975353) ≤ (680747117 / 1000000000) := by
  have h := checkLog_sound (w := (975353 / 2975353)) (n := 12)
    (lo := (170186779 / 250000000)) (hi := (680747117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975353 / 1000000) = 1/(1000000 / 1975353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170186779 / 250000000) (680747117 / 1000000000) (Real.log (1975353 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975353 / 1000000) = -Real.log (1000000 / 1975353) := by
    rw [show ((1975353 / 1000000) : ℝ) = ((1000000 / 1975353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1851550043 / 500000000) ≤ -Real.log (24647 / 1000000) ∧
    -Real.log (24647 / 1000000) ≤ (925775023 / 250000000) := by
  have h := checkLog_sound (w := (6603 / 55897)) (n := 12)
    (lo := (118682093 / 500000000)) (hi := (237364187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24647) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24647) = 1/(24647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-925775023 / 250000000) (-1851550043 / 500000000) (Real.log (24647 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4383641827 / 1000000000) ≤ -Real.log (125000000000 / 10016165017037) ∧
    -Real.log (125000000000 / 10016165017037) ≤ (2191820917 / 500000000) := by
  have h := checkLog_sound (w := (2016165017037 / 18016165017037)) (n := 12)
    (lo := (224758747 / 1000000000)) (hi := (56189687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10016165017037 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10016165017037 / 8000000000000) = 1/(125000000000 / 10016165017037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4383641827 / 1000000000) (2191820917 / 500000000) (Real.log (10016165017037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10016165017037 / 125000000000) = -Real.log (125000000000 / 10016165017037) := by
    rw [show ((10016165017037 / 125000000000) : ℝ) = ((125000000000 / 10016165017037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (274361233 / 62500000) ≤ -Real.log (500000000000 / 40311329224993) ∧
    -Real.log (500000000000 / 40311329224993) ≤ (877955947 / 200000000) := by
  have h := checkLog_sound (w := (8311329224993 / 72311329224993)) (n := 12)
    (lo := (28862081 / 125000000)) (hi := (230896649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40311329224993 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40311329224993 / 32000000000000) = 1/(500000000000 / 40311329224993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (274361233 / 62500000) (877955947 / 200000000) (Real.log (40311329224993 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40311329224993 / 500000000000) = -Real.log (500000000000 / 40311329224993) := by
    rw [show ((40311329224993 / 500000000000) : ℝ) = ((500000000000 / 40311329224993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2188831471 / 500000000) ≤ -Real.log (100000000000 / 7965166545689) ∧
    -Real.log (100000000000 / 7965166545689) ≤ (4377662949 / 1000000000) := by
  have h := checkLog_sound (w := (1565166545689 / 14365166545689)) (n := 12)
    (lo := (109389931 / 500000000)) (hi := (218779863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7965166545689 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7965166545689 / 6400000000000) = 1/(100000000000 / 7965166545689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2188831471 / 500000000) (4377662949 / 1000000000) (Real.log (7965166545689 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7965166545689 / 100000000000) = -Real.log (100000000000 / 7965166545689) := by
    rw [show ((7965166545689 / 100000000000) : ℝ) = ((100000000000 / 7965166545689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2191923601 / 500000000) ≤ -Real.log (6250000000 / 500911114943) ∧
    -Real.log (6250000000 / 500911114943) ≤ (4383847209 / 1000000000) := by
  have h := checkLog_sound (w := (100911114943 / 900911114943)) (n := 12)
    (lo := (112482061 / 500000000)) (hi := (224964123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500911114943 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(500911114943 / 400000000000) = 1/(6250000000 / 500911114943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2191923601 / 500000000) (4383847209 / 1000000000) (Real.log (500911114943 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (500911114943 / 6250000000) = -Real.log (6250000000 / 500911114943) := by
    rw [show ((500911114943 / 6250000000) : ℝ) = ((6250000000 / 500911114943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0058Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058
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

theorem reflection_log_1_neg : (678306149 / 1000000000) ≤ -Real.log (102400 / 201783) ∧
    -Real.log (102400 / 201783) ≤ (13566123 / 20000000) := by
  have h := checkLog_sound (w := (99383 / 304183)) (n := 12)
    (lo := (678306149 / 1000000000)) (hi := (13566123 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201783 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201783 / 102400) = 1/(102400 / 201783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678306149 / 1000000000) (13566123 / 20000000) (Real.log (201783 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201783 / 102400) = -Real.log (102400 / 201783) := by
    rw [show ((201783 / 102400) : ℝ) = ((102400 / 201783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3524623749 / 1000000000) ≤ -Real.log (3017 / 102400) ∧
    -Real.log (3017 / 102400) ≤ (704924751 / 200000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3017) = 1/(3017 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-704924751 / 200000000) (-3524623749 / 1000000000) (Real.log (3017 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42388249 / 62500000) ≤ -Real.log (25600 / 50441) ∧
    -Real.log (25600 / 50441) ≤ (135642397 / 200000000) := by
  have h := checkLog_sound (w := (24841 / 76041)) (n := 12)
    (lo := (42388249 / 62500000)) (hi := (135642397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50441 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50441 / 25600) = 1/(25600 / 50441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42388249 / 62500000) (135642397 / 200000000) (Real.log (50441 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50441 / 25600) = -Real.log (25600 / 50441) := by
    rw [show ((50441 / 25600) : ℝ) = ((25600 / 50441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (70366917 / 20000000) ≤ -Real.log (759 / 25600) ∧
    -Real.log (759 / 25600) ≤ (27487077 / 7812500) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 759) = 1/(759 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-27487077 / 7812500) (-70366917 / 20000000) (Real.log (759 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (33162077 / 50000000) ≤ -Real.log (51200 / 99383) ∧
    -Real.log (51200 / 99383) ≤ (663241541 / 1000000000) := by
  have h := checkLog_sound (w := (48183 / 150583)) (n := 12)
    (lo := (33162077 / 50000000)) (hi := (663241541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99383 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99383 / 51200) = 1/(51200 / 99383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (33162077 / 50000000) (663241541 / 1000000000) (Real.log (99383 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99383 / 51200) = -Real.log (51200 / 99383) := by
    rw [show ((99383 / 51200) : ℝ) = ((51200 / 99383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2831476569 / 1000000000) ≤ -Real.log (3017 / 51200) ∧
    -Real.log (3017 / 51200) ≤ (1415738287 / 500000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3017) = 1/(3017 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1415738287 / 500000000) (-2831476569 / 1000000000) (Real.log (3017 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331525171 / 500000000) ≤ -Real.log (12800 / 24841) ∧
    -Real.log (12800 / 24841) ≤ (663050343 / 1000000000) := by
  have h := checkLog_sound (w := (12041 / 37641)) (n := 12)
    (lo := (331525171 / 500000000)) (hi := (663050343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24841 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24841 / 12800) = 1/(12800 / 24841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331525171 / 500000000) (663050343 / 1000000000) (Real.log (24841 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24841 / 12800) = -Real.log (12800 / 24841) := by
    rw [show ((24841 / 12800) : ℝ) = ((12800 / 24841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (282519867 / 100000000) ≤ -Real.log (759 / 12800) ∧
    -Real.log (759 / 12800) ≤ (113007947 / 40000000) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 759) = 1/(759 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-113007947 / 40000000) (-282519867 / 100000000) (Real.log (759 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680669659 / 1000000000) ≤ -Real.log (1250 / 2469) ∧
    -Real.log (1250 / 2469) ≤ (34033483 / 50000000) := by
  have h := checkLog_sound (w := (1219 / 3719)) (n := 12)
    (lo := (680669659 / 1000000000)) (hi := (34033483 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 1250) = 1/(1250 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680669659 / 1000000000) (34033483 / 50000000) (Real.log (2469 / 1250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (2469 / 1250) = -Real.log (1250 / 2469) := by
    rw [show ((2469 / 1250) : ℝ) = ((1250 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3696911623 / 1000000000) ≤ -Real.log (31 / 1250) ∧
    -Real.log (31 / 1250) ≤ (3696911629 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1121)) (n := 12)
    (lo := (231175723 / 1000000000)) (hi := (57793931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 496) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 496) = 1/(31 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3696911629 / 1000000000) (-3696911623 / 1000000000) (Real.log (31 / 1250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680745091 / 1000000000) ≤ -Real.log (1000000 / 1975349) ∧
    -Real.log (1000000 / 1975349) ≤ (170186273 / 250000000) := by
  have h := checkLog_sound (w := (975349 / 2975349)) (n := 12)
    (lo := (680745091 / 1000000000)) (hi := (170186273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975349 / 1000000) = 1/(1000000 / 1975349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680745091 / 1000000000) (170186273 / 250000000) (Real.log (1975349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975349 / 1000000) = -Real.log (1000000 / 1975349) := by
    rw [show ((1975349 / 1000000) : ℝ) = ((1000000 / 1975349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (231433613 / 62500000) ≤ -Real.log (24651 / 1000000) ∧
    -Real.log (24651 / 1000000) ≤ (1851468907 / 500000000) := by
  have h := checkLog_sound (w := (6599 / 55901)) (n := 12)
    (lo := (59300477 / 250000000)) (hi := (237201909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24651) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24651) = 1/(24651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1851468907 / 500000000) (-231433613 / 62500000) (Real.log (24651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680594727 / 1000000000) ≤ -Real.log (250000 / 493763) ∧
    -Real.log (250000 / 493763) ≤ (85074341 / 125000000) := by
  have h := checkLog_sound (w := (243763 / 743763)) (n := 12)
    (lo := (680594727 / 1000000000)) (hi := (85074341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493763 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493763 / 250000) = 1/(250000 / 493763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680594727 / 1000000000) (85074341 / 125000000) (Real.log (493763 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493763 / 250000) = -Real.log (250000 / 493763) := by
    rw [show ((493763 / 250000) : ℝ) = ((250000 / 493763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3690961617 / 1000000000) ≤ -Real.log (6237 / 250000) ∧
    -Real.log (6237 / 250000) ≤ (3690961623 / 1000000000) := by
  have h := checkLog_sound (w := (3151 / 28099)) (n := 12)
    (lo := (225225717 / 1000000000)) (hi := (112612859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12474) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12474) = 1/(6237 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3690961623 / 1000000000) (-3690961617 / 1000000000) (Real.log (6237 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680671177 / 1000000000) ≤ -Real.log (1000000 / 1975203) ∧
    -Real.log (1000000 / 1975203) ≤ (340335589 / 500000000) := by
  have h := checkLog_sound (w := (975203 / 2975203)) (n := 12)
    (lo := (680671177 / 1000000000)) (hi := (340335589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975203 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975203 / 1000000) = 1/(1000000 / 1975203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680671177 / 1000000000) (340335589 / 500000000) (Real.log (1975203 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975203 / 1000000) = -Real.log (1000000 / 1975203) := by
    rw [show ((1975203 / 1000000) : ℝ) = ((1000000 / 1975203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1848516299 / 500000000) ≤ -Real.log (24797 / 1000000) ∧
    -Real.log (24797 / 1000000) ≤ (924258151 / 250000000) := by
  have h := checkLog_sound (w := (6453 / 56047)) (n := 12)
    (lo := (115648349 / 500000000)) (hi := (231296699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24797) = 1/(24797 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-924258151 / 250000000) (-1848516299 / 500000000) (Real.log (24797 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4377581281 / 1000000000) ≤ -Real.log (500000000000 / 39822580645161) ∧
    -Real.log (500000000000 / 39822580645161) ≤ (547197661 / 125000000) := by
  have h := checkLog_sound (w := (7822580645161 / 71822580645161)) (n := 12)
    (lo := (218698201 / 1000000000)) (hi := (109349101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39822580645161 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39822580645161 / 32000000000000) = 1/(500000000000 / 39822580645161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4377581281 / 1000000000) (547197661 / 125000000) (Real.log (39822580645161 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39822580645161 / 500000000000) = -Real.log (500000000000 / 39822580645161) := by
    rw [show ((39822580645161 / 500000000000) : ℝ) = ((500000000000 / 39822580645161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4383682899 / 1000000000) ≤ -Real.log (500000000000 / 40066305626547) ∧
    -Real.log (500000000000 / 40066305626547) ≤ (2191841453 / 500000000) := by
  have h := checkLog_sound (w := (8066305626547 / 72066305626547)) (n := 12)
    (lo := (224799819 / 1000000000)) (hi := (11239991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40066305626547 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40066305626547 / 32000000000000) = 1/(500000000000 / 40066305626547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4383682899 / 1000000000) (2191841453 / 500000000) (Real.log (40066305626547 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40066305626547 / 500000000000) = -Real.log (500000000000 / 40066305626547) := by
    rw [show ((40066305626547 / 500000000000) : ℝ) = ((500000000000 / 40066305626547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (546444543 / 125000000) ≤ -Real.log (250000000000 / 19791686708353) ∧
    -Real.log (250000000000 / 19791686708353) ≤ (4371556351 / 1000000000) := by
  have h := checkLog_sound (w := (3791686708353 / 35791686708353)) (n := 12)
    (lo := (13292079 / 62500000)) (hi := (42534653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19791686708353 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19791686708353 / 16000000000000) = 1/(250000000000 / 19791686708353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (546444543 / 125000000) (4371556351 / 1000000000) (Real.log (19791686708353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19791686708353 / 250000000000) = -Real.log (250000000000 / 19791686708353) := by
    rw [show ((19791686708353 / 250000000000) : ℝ) = ((250000000000 / 19791686708353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (175108151 / 40000000) ≤ -Real.log (500000000000 / 39827458966811) ∧
    -Real.log (500000000000 / 39827458966811) ≤ (2188851891 / 500000000) := by
  have h := checkLog_sound (w := (7827458966811 / 71827458966811)) (n := 12)
    (lo := (43764139 / 200000000)) (hi := (27352587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39827458966811 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39827458966811 / 32000000000000) = 1/(500000000000 / 39827458966811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (175108151 / 40000000) (2188851891 / 500000000) (Real.log (39827458966811 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39827458966811 / 500000000000) = -Real.log (500000000000 / 39827458966811) := by
    rw [show ((39827458966811 / 500000000000) : ℝ) = ((500000000000 / 39827458966811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0059Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059
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

theorem reflection_log_1_neg : (42388249 / 62500000) ≤ -Real.log (25600 / 50441) ∧
    -Real.log (25600 / 50441) ≤ (135642397 / 200000000) := by
  have h := checkLog_sound (w := (24841 / 76041)) (n := 12)
    (lo := (42388249 / 62500000)) (hi := (135642397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50441 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50441 / 25600) = 1/(25600 / 50441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42388249 / 62500000) (135642397 / 200000000) (Real.log (50441 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50441 / 25600) = -Real.log (25600 / 50441) := by
    rw [show ((50441 / 25600) : ℝ) = ((25600 / 50441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (70366917 / 20000000) ≤ -Real.log (759 / 25600) ∧
    -Real.log (759 / 25600) ≤ (27487077 / 7812500) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 759) = 1/(759 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-27487077 / 7812500) (-70366917 / 20000000) (Real.log (759 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678117811 / 1000000000) ≤ -Real.log (20480 / 40349) ∧
    -Real.log (20480 / 40349) ≤ (169529453 / 250000000) := by
  have h := checkLog_sound (w := (19869 / 60829)) (n := 12)
    (lo := (678117811 / 1000000000)) (hi := (169529453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40349 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40349 / 20480) = 1/(20480 / 40349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678117811 / 1000000000) (169529453 / 250000000) (Real.log (40349 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40349 / 20480) = -Real.log (20480 / 40349) := by
    rw [show ((40349 / 20480) : ℝ) = ((20480 / 40349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3512107117 / 1000000000) ≤ -Real.log (611 / 20480) ∧
    -Real.log (611 / 20480) ≤ (3512107123 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 611) = 1/(611 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3512107123 / 1000000000) (-3512107117 / 1000000000) (Real.log (611 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331525171 / 500000000) ≤ -Real.log (12800 / 24841) ∧
    -Real.log (12800 / 24841) ≤ (663050343 / 1000000000) := by
  have h := checkLog_sound (w := (12041 / 37641)) (n := 12)
    (lo := (331525171 / 500000000)) (hi := (663050343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24841 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24841 / 12800) = 1/(12800 / 24841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (331525171 / 500000000) (663050343 / 1000000000) (Real.log (24841 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24841 / 12800) = -Real.log (12800 / 24841) := by
    rw [show ((24841 / 12800) : ℝ) = ((12800 / 24841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282519867 / 100000000) ≤ -Real.log (759 / 12800) ∧
    -Real.log (759 / 12800) ≤ (113007947 / 40000000) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 759) = 1/(759 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-113007947 / 40000000) (-282519867 / 100000000) (Real.log (759 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165714777 / 250000000) ≤ -Real.log (10240 / 19869) ∧
    -Real.log (10240 / 19869) ≤ (662859109 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 30109)) (n := 12)
    (lo := (165714777 / 250000000)) (hi := (662859109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19869 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19869 / 10240) = 1/(10240 / 19869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165714777 / 250000000) (662859109 / 1000000000) (Real.log (19869 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19869 / 10240) = -Real.log (10240 / 19869) := by
    rw [show ((19869 / 10240) : ℝ) = ((10240 / 19869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2818959937 / 1000000000) ≤ -Real.log (611 / 10240) ∧
    -Real.log (611 / 10240) ≤ (1409479971 / 500000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 611) = 1/(611 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1409479971 / 500000000) (-2818959937 / 1000000000) (Real.log (611 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680594727 / 1000000000) ≤ -Real.log (250000 / 493763) ∧
    -Real.log (250000 / 493763) ≤ (85074341 / 125000000) := by
  have h := checkLog_sound (w := (243763 / 743763)) (n := 12)
    (lo := (680594727 / 1000000000)) (hi := (85074341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493763 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493763 / 250000) = 1/(250000 / 493763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680594727 / 1000000000) (85074341 / 125000000) (Real.log (493763 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493763 / 250000) = -Real.log (250000 / 493763) := by
    rw [show ((493763 / 250000) : ℝ) = ((250000 / 493763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3690961617 / 1000000000) ≤ -Real.log (6237 / 250000) ∧
    -Real.log (6237 / 250000) ≤ (3690961623 / 1000000000) := by
  have h := checkLog_sound (w := (3151 / 28099)) (n := 12)
    (lo := (225225717 / 1000000000)) (hi := (112612859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12474) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12474) = 1/(6237 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3690961623 / 1000000000) (-3690961617 / 1000000000) (Real.log (6237 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136134033 / 200000000) ≤ -Real.log (1000000 / 1975201) ∧
    -Real.log (1000000 / 1975201) ≤ (340335083 / 500000000) := by
  have h := checkLog_sound (w := (975201 / 2975201)) (n := 12)
    (lo := (136134033 / 200000000)) (hi := (340335083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975201 / 1000000) = 1/(1000000 / 1975201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136134033 / 200000000) (340335083 / 500000000) (Real.log (1975201 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975201 / 1000000) = -Real.log (1000000 / 1975201) := by
    rw [show ((1975201 / 1000000) : ℝ) = ((1000000 / 1975201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1848475973 / 500000000) ≤ -Real.log (24799 / 1000000) ∧
    -Real.log (24799 / 1000000) ≤ (231059497 / 62500000) := by
  have h := checkLog_sound (w := (6451 / 56049)) (n := 12)
    (lo := (115608023 / 500000000)) (hi := (231216047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24799) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24799) = 1/(24799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-231059497 / 62500000) (-1848475973 / 500000000) (Real.log (24799 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85064847 / 125000000) ≤ -Real.log (500000 / 987451) ∧
    -Real.log (500000 / 987451) ≤ (680518777 / 1000000000) := by
  have h := checkLog_sound (w := (487451 / 1487451)) (n := 12)
    (lo := (85064847 / 125000000)) (hi := (680518777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987451 / 500000) = 1/(500000 / 987451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85064847 / 125000000) (680518777 / 1000000000) (Real.log (987451 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987451 / 500000) = -Real.log (500000 / 987451) := by
    rw [show ((987451 / 500000) : ℝ) = ((500000 / 987451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1842483557 / 500000000) ≤ -Real.log (12549 / 500000) ∧
    -Real.log (12549 / 500000) ≤ (46062089 / 12500000) := by
  have h := checkLog_sound (w := (1538 / 14087)) (n := 12)
    (lo := (109615607 / 500000000)) (hi := (43846243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12549) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12549) = 1/(12549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46062089 / 12500000) (-1842483557 / 500000000) (Real.log (12549 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680595233 / 1000000000) ≤ -Real.log (1000000 / 1975053) ∧
    -Real.log (1000000 / 1975053) ≤ (340297617 / 500000000) := by
  have h := checkLog_sound (w := (975053 / 2975053)) (n := 12)
    (lo := (680595233 / 1000000000)) (hi := (340297617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975053 / 1000000) = 1/(1000000 / 1975053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680595233 / 1000000000) (340297617 / 500000000) (Real.log (1975053 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975053 / 1000000) = -Real.log (1000000 / 1975053) := by
    rw [show ((1975053 / 1000000) : ℝ) = ((1000000 / 1975053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3691001701 / 1000000000) ≤ -Real.log (24947 / 1000000) ∧
    -Real.log (24947 / 1000000) ≤ (3691001707 / 1000000000) := by
  have h := checkLog_sound (w := (6303 / 56197)) (n := 12)
    (lo := (225265801 / 1000000000)) (hi := (112632901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24947) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24947) = 1/(24947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3691001707 / 1000000000) (-3691001701 / 1000000000) (Real.log (24947 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (546444543 / 125000000) ≤ -Real.log (250000000000 / 19791686708353) ∧
    -Real.log (250000000000 / 19791686708353) ≤ (4371556351 / 1000000000) := by
  have h := checkLog_sound (w := (3791686708353 / 35791686708353)) (n := 12)
    (lo := (13292079 / 62500000)) (hi := (42534653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19791686708353 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19791686708353 / 16000000000000) = 1/(250000000000 / 19791686708353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (546444543 / 125000000) (4371556351 / 1000000000) (Real.log (19791686708353 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19791686708353 / 250000000000) = -Real.log (250000000000 / 19791686708353) := by
    rw [show ((19791686708353 / 250000000000) : ℝ) = ((250000000000 / 19791686708353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4377622111 / 1000000000) ≤ -Real.log (100000000000 / 7964841324247) ∧
    -Real.log (100000000000 / 7964841324247) ≤ (2188811059 / 500000000) := by
  have h := checkLog_sound (w := (1564841324247 / 14364841324247)) (n := 12)
    (lo := (218739031 / 1000000000)) (hi := (27342379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7964841324247 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7964841324247 / 6400000000000) = 1/(100000000000 / 7964841324247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4377622111 / 1000000000) (2188811059 / 500000000) (Real.log (7964841324247 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7964841324247 / 100000000000) = -Real.log (100000000000 / 7964841324247) := by
    rw [show ((7964841324247 / 100000000000) : ℝ) = ((100000000000 / 7964841324247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (436548589 / 100000000) ≤ -Real.log (125000000000 / 9835953063989) ∧
    -Real.log (125000000000 / 9835953063989) ≤ (4365485897 / 1000000000) := by
  have h := checkLog_sound (w := (1835953063989 / 17835953063989)) (n := 12)
    (lo := (20660281 / 100000000)) (hi := (206602811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9835953063989 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9835953063989 / 8000000000000) = 1/(125000000000 / 9835953063989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (436548589 / 100000000) (4365485897 / 1000000000) (Real.log (9835953063989 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9835953063989 / 125000000000) = -Real.log (125000000000 / 9835953063989) := by
    rw [show ((9835953063989 / 125000000000) : ℝ) = ((125000000000 / 9835953063989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2185798467 / 500000000) ≤ -Real.log (100000000000 / 7916996031587) ∧
    -Real.log (100000000000 / 7916996031587) ≤ (4371596941 / 1000000000) := by
  have h := checkLog_sound (w := (1516996031587 / 14316996031587)) (n := 12)
    (lo := (106356927 / 500000000)) (hi := (42542771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7916996031587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7916996031587 / 6400000000000) = 1/(100000000000 / 7916996031587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2185798467 / 500000000) (4371596941 / 1000000000) (Real.log (7916996031587 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7916996031587 / 100000000000) = -Real.log (100000000000 / 7916996031587) := by
    rw [show ((7916996031587 / 100000000000) : ℝ) = ((100000000000 / 7916996031587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059

end


