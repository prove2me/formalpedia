-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0092Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0092Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:45:57.074349+00:00
-- url     : https://prove2.me/theorems/35cea309-ac5b-4308-ad12-e86b6116b805
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0098Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0098Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0098Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0092Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0093Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0094Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0095Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0096Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0097Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0098Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0092
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

theorem reflection_log_1_neg : (672924543 / 1000000000) ≤ -Real.log (1024 / 2007) ∧
    -Real.log (1024 / 2007) ≤ (5257223 / 7812500) := by
  have h := checkLog_sound (w := (983 / 3031)) (n := 12)
    (lo := (672924543 / 1000000000)) (hi := (5257223 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2007 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2007 / 1024) = 1/(1024 / 2007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672924543 / 1000000000) (5257223 / 7812500) (Real.log (2007 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2007 / 1024) = -Real.log (1024 / 2007) := by
    rw [show ((2007 / 1024) : ℝ) = ((1024 / 2007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (402237467 / 125000000) ≤ -Real.log (41 / 1024) ∧
    -Real.log (41 / 1024) ≤ (3217899741 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 41) = 1/(41 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3217899741 / 1000000000) (-402237467 / 125000000) (Real.log (41 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672735187 / 1000000000) ≤ -Real.log (51200 / 100331) ∧
    -Real.log (51200 / 100331) ≤ (168183797 / 250000000) := by
  have h := checkLog_sound (w := (49131 / 151531)) (n := 12)
    (lo := (672735187 / 1000000000)) (hi := (168183797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100331 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100331 / 51200) = 1/(51200 / 100331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672735187 / 1000000000) (168183797 / 250000000) (Real.log (100331 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100331 / 51200) = -Real.log (51200 / 100331) := by
    rw [show ((100331 / 51200) : ℝ) = ((51200 / 100331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3208674131 / 1000000000) ≤ -Real.log (2069 / 51200) ∧
    -Real.log (2069 / 51200) ≤ (401084267 / 125000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2069) = 1/(2069 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-401084267 / 125000000) (-3208674131 / 1000000000) (Real.log (2069 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (130456899 / 200000000) ≤ -Real.log (512 / 983) ∧
    -Real.log (512 / 983) ≤ (40767781 / 62500000) := by
  have h := checkLog_sound (w := (471 / 1495)) (n := 12)
    (lo := (130456899 / 200000000)) (hi := (40767781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 512) = 1/(512 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (130456899 / 200000000) (40767781 / 62500000) (Real.log (983 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (983 / 512) = -Real.log (512 / 983) := by
    rw [show ((983 / 512) : ℝ) = ((512 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (631188139 / 250000000) ≤ -Real.log (41 / 512) ∧
    -Real.log (41 / 512) ≤ (31559407 / 12500000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 41) = 1/(41 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31559407 / 12500000) (-631188139 / 250000000) (Real.log (41 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81487231 / 125000000) ≤ -Real.log (25600 / 49131) ∧
    -Real.log (25600 / 49131) ≤ (651897849 / 1000000000) := by
  have h := checkLog_sound (w := (23531 / 74731)) (n := 12)
    (lo := (81487231 / 125000000)) (hi := (651897849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49131 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49131 / 25600) = 1/(25600 / 49131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81487231 / 125000000) (651897849 / 1000000000) (Real.log (49131 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49131 / 25600) = -Real.log (25600 / 49131) := by
    rw [show ((49131 / 25600) : ℝ) = ((25600 / 49131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2515526951 / 1000000000) ≤ -Real.log (2069 / 25600) ∧
    -Real.log (2069 / 25600) ≤ (503105391 / 200000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2069) = 1/(2069 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-503105391 / 200000000) (-2515526951 / 1000000000) (Real.log (2069 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135275063 / 200000000) ≤ -Real.log (62500 / 122921) ∧
    -Real.log (62500 / 122921) ≤ (169093829 / 250000000) := by
  have h := checkLog_sound (w := (60421 / 185421)) (n := 12)
    (lo := (135275063 / 200000000)) (hi := (169093829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122921 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122921 / 62500) = 1/(62500 / 122921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135275063 / 200000000) (169093829 / 250000000) (Real.log (122921 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (122921 / 62500) = -Real.log (62500 / 122921) := by
    rw [show ((122921 / 62500) : ℝ) = ((62500 / 122921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (680655909 / 200000000) ≤ -Real.log (2079 / 62500) ∧
    -Real.log (2079 / 62500) ≤ (68065591 / 20000000) := by
  have h := checkLog_sound (w := (7309 / 23941)) (n := 12)
    (lo := (25227633 / 40000000)) (hi := (315345413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8316) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8316) = 1/(2079 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68065591 / 20000000) (-680655909 / 200000000) (Real.log (2079 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676522757 / 1000000000) ≤ -Real.log (500000 / 983513) ∧
    -Real.log (500000 / 983513) ≤ (338261379 / 500000000) := by
  have h := checkLog_sound (w := (483513 / 1483513)) (n := 12)
    (lo := (676522757 / 1000000000)) (hi := (338261379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983513 / 500000) = 1/(500000 / 983513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676522757 / 1000000000) (338261379 / 500000000) (Real.log (983513 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983513 / 500000) = -Real.log (500000 / 983513) := by
    rw [show ((983513 / 500000) : ℝ) = ((500000 / 983513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53313061 / 15625000) ≤ -Real.log (16487 / 500000) ∧
    -Real.log (16487 / 500000) ≤ (3412035909 / 1000000000) := by
  have h := checkLog_sound (w := (14763 / 47737)) (n := 12)
    (lo := (39965449 / 62500000)) (hi := (127889437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16487) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16487) = 1/(16487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3412035909 / 1000000000) (-53313061 / 15625000) (Real.log (16487 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676224801 / 1000000000) ≤ -Real.log (25000 / 49161) ∧
    -Real.log (25000 / 49161) ≤ (338112401 / 500000000) := by
  have h := checkLog_sound (w := (24161 / 74161)) (n := 12)
    (lo := (676224801 / 1000000000)) (hi := (338112401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49161 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49161 / 25000) = 1/(25000 / 49161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676224801 / 1000000000) (338112401 / 500000000) (Real.log (49161 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (49161 / 25000) = -Real.log (25000 / 49161) := by
    rw [show ((49161 / 25000) : ℝ) = ((25000 / 49161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (678884079 / 200000000) ≤ -Real.log (839 / 25000) ∧
    -Real.log (839 / 25000) ≤ (8486051 / 2500000) := by
  have h := checkLog_sound (w := (1447 / 4803)) (n := 12)
    (lo := (24873267 / 40000000)) (hi := (155457919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1678) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1678) = 1/(839 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8486051 / 2500000) (-678884079 / 200000000) (Real.log (839 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676374807 / 1000000000) ≤ -Real.log (200000 / 393347) ∧
    -Real.log (200000 / 393347) ≤ (84546851 / 125000000) := by
  have h := checkLog_sound (w := (193347 / 593347)) (n := 12)
    (lo := (676374807 / 1000000000)) (hi := (84546851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393347 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393347 / 200000) = 1/(200000 / 393347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676374807 / 1000000000) (84546851 / 125000000) (Real.log (393347 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393347 / 200000) = -Real.log (200000 / 393347) := by
    rw [show ((393347 / 200000) : ℝ) = ((200000 / 393347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3403249483 / 1000000000) ≤ -Real.log (6653 / 200000) ∧
    -Real.log (6653 / 200000) ≤ (212703093 / 62500000) := by
  have h := checkLog_sound (w := (5847 / 19153)) (n := 12)
    (lo := (630660763 / 1000000000)) (hi := (157665191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6653) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6653) = 1/(6653 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-212703093 / 62500000) (-3403249483 / 1000000000) (Real.log (6653 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (203982743 / 50000000) ≤ -Real.log (50000000000 / 2956253006253) ∧
    -Real.log (50000000000 / 2956253006253) ≤ (2039827433 / 500000000) := by
  have h := checkLog_sound (w := (1356253006253 / 4556253006253)) (n := 12)
    (lo := (7673987 / 12500000)) (hi := (613918961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2956253006253 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2956253006253 / 1600000000000) = 1/(50000000000 / 2956253006253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (203982743 / 50000000) (2039827433 / 500000000) (Real.log (2956253006253 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2956253006253 / 50000000000) = -Real.log (50000000000 / 2956253006253) := by
    rw [show ((2956253006253 / 50000000000) : ℝ) = ((50000000000 / 2956253006253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4088558661 / 1000000000) ≤ -Real.log (31250000000 / 1864182765209) ∧
    -Real.log (31250000000 / 1864182765209) ≤ (4088558667 / 1000000000) := by
  have h := checkLog_sound (w := (864182765209 / 2864182765209)) (n := 12)
    (lo := (622822761 / 1000000000)) (hi := (311411381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1864182765209 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1864182765209 / 1000000000000) = 1/(31250000000 / 1864182765209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4088558661 / 1000000000) (4088558667 / 1000000000) (Real.log (1864182765209 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1864182765209 / 31250000000) = -Real.log (31250000000 / 1864182765209) := by
    rw [show ((1864182765209 / 31250000000) : ℝ) = ((31250000000 / 1864182765209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (814129039 / 200000000) ≤ -Real.log (2000000000 / 117189511323) ∧
    -Real.log (2000000000 / 117189511323) ≤ (4070645201 / 1000000000) := by
  have h := checkLog_sound (w := (53189511323 / 181189511323)) (n := 12)
    (lo := (120981859 / 200000000)) (hi := (37806831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117189511323 / 64000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(117189511323 / 64000000000) = 1/(2000000000 / 117189511323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (814129039 / 200000000) (4070645201 / 1000000000) (Real.log (117189511323 / 2000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (117189511323 / 2000000000) = -Real.log (2000000000 / 117189511323) := by
    rw [show ((117189511323 / 2000000000) : ℝ) = ((2000000000 / 117189511323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (407962429 / 100000000) ≤ -Real.log (100000000000 / 5912325266797) ∧
    -Real.log (100000000000 / 5912325266797) ≤ (509953037 / 125000000) := by
  have h := checkLog_sound (w := (2712325266797 / 9112325266797)) (n := 12)
    (lo := (61388839 / 100000000)) (hi := (613888391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5912325266797 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5912325266797 / 3200000000000) = 1/(100000000000 / 5912325266797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (407962429 / 100000000) (509953037 / 125000000) (Real.log (5912325266797 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5912325266797 / 100000000000) = -Real.log (100000000000 / 5912325266797) := by
    rw [show ((5912325266797 / 100000000000) : ℝ) = ((100000000000 / 5912325266797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0092

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0093
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

theorem reflection_log_1_neg : (672735187 / 1000000000) ≤ -Real.log (51200 / 100331) ∧
    -Real.log (51200 / 100331) ≤ (168183797 / 250000000) := by
  have h := checkLog_sound (w := (49131 / 151531)) (n := 12)
    (lo := (672735187 / 1000000000)) (hi := (168183797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100331 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100331 / 51200) = 1/(51200 / 100331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672735187 / 1000000000) (168183797 / 250000000) (Real.log (100331 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100331 / 51200) = -Real.log (51200 / 100331) := by
    rw [show ((100331 / 51200) : ℝ) = ((51200 / 100331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3208674131 / 1000000000) ≤ -Real.log (2069 / 51200) ∧
    -Real.log (2069 / 51200) ≤ (401084267 / 125000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2069) = 1/(2069 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-401084267 / 125000000) (-3208674131 / 1000000000) (Real.log (2069 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (168136449 / 250000000) ≤ -Real.log (6400 / 12539) ∧
    -Real.log (6400 / 12539) ≤ (672545797 / 1000000000) := by
  have h := checkLog_sound (w := (6139 / 18939)) (n := 12)
    (lo := (168136449 / 250000000)) (hi := (672545797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12539 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12539 / 6400) = 1/(6400 / 12539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (168136449 / 250000000) (672545797 / 1000000000) (Real.log (12539 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12539 / 6400) = -Real.log (6400 / 12539) := by
    rw [show ((12539 / 6400) : ℝ) = ((6400 / 12539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3199532859 / 1000000000) ≤ -Real.log (261 / 6400) ∧
    -Real.log (261 / 6400) ≤ (49992701 / 15625000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 261) = 1/(261 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49992701 / 15625000) (-3199532859 / 1000000000) (Real.log (261 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81487231 / 125000000) ≤ -Real.log (25600 / 49131) ∧
    -Real.log (25600 / 49131) ≤ (651897849 / 1000000000) := by
  have h := checkLog_sound (w := (23531 / 74731)) (n := 12)
    (lo := (81487231 / 125000000)) (hi := (651897849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49131 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49131 / 25600) = 1/(25600 / 49131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81487231 / 125000000) (651897849 / 1000000000) (Real.log (49131 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49131 / 25600) = -Real.log (25600 / 49131) := by
    rw [show ((49131 / 25600) : ℝ) = ((25600 / 49131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2515526951 / 1000000000) ≤ -Real.log (2069 / 25600) ∧
    -Real.log (2069 / 25600) ≤ (503105391 / 200000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2069) = 1/(2069 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-503105391 / 200000000) (-2515526951 / 1000000000) (Real.log (2069 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (162877763 / 250000000) ≤ -Real.log (3200 / 6139) ∧
    -Real.log (3200 / 6139) ≤ (651511053 / 1000000000) := by
  have h := checkLog_sound (w := (2939 / 9339)) (n := 12)
    (lo := (162877763 / 250000000)) (hi := (651511053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6139 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6139 / 3200) = 1/(3200 / 6139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (162877763 / 250000000) (651511053 / 1000000000) (Real.log (6139 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6139 / 3200) = -Real.log (3200 / 6139) := by
    rw [show ((6139 / 3200) : ℝ) = ((3200 / 6139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2506385679 / 1000000000) ≤ -Real.log (261 / 3200) ∧
    -Real.log (261 / 3200) ≤ (2506385683 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 261) = 1/(261 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2506385683 / 1000000000) (-2506385679 / 1000000000) (Real.log (261 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (676228869 / 1000000000) ≤ -Real.log (62500 / 122903) ∧
    -Real.log (62500 / 122903) ≤ (67622887 / 100000000) := by
  have h := checkLog_sound (w := (60403 / 185403)) (n := 12)
    (lo := (676228869 / 1000000000)) (hi := (67622887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122903 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122903 / 62500) = 1/(62500 / 122903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (676228869 / 1000000000) (67622887 / 100000000) (Real.log (122903 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (122903 / 62500) = -Real.log (62500 / 122903) := by
    rw [show ((122903 / 62500) : ℝ) = ((62500 / 122903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1697329401 / 500000000) ≤ -Real.log (2097 / 62500) ∧
    -Real.log (2097 / 62500) ≤ (3394658807 / 1000000000) := by
  have h := checkLog_sound (w := (7237 / 24013)) (n := 12)
    (lo := (311035041 / 500000000)) (hi := (622070083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8388) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8388) = 1/(2097 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3394658807 / 1000000000) (-1697329401 / 500000000) (Real.log (2097 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42273489 / 62500000) ≤ -Real.log (1000000 / 1966737) ∧
    -Real.log (1000000 / 1966737) ≤ (27055033 / 40000000) := by
  have h := checkLog_sound (w := (966737 / 2966737)) (n := 12)
    (lo := (42273489 / 62500000)) (hi := (27055033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966737 / 1000000) = 1/(1000000 / 1966737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42273489 / 62500000) (27055033 / 40000000) (Real.log (1966737 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1966737 / 1000000) = -Real.log (1000000 / 1966737) := by
    rw [show ((1966737 / 1000000) : ℝ) = ((1000000 / 1966737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (425413701 / 125000000) ≤ -Real.log (33263 / 1000000) ∧
    -Real.log (33263 / 1000000) ≤ (3403309613 / 1000000000) := by
  have h := checkLog_sound (w := (29237 / 95763)) (n := 12)
    (lo := (78840111 / 125000000)) (hi := (630720889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33263) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33263) = 1/(33263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3403309613 / 1000000000) (-425413701 / 125000000) (Real.log (33263 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676075281 / 1000000000) ≤ -Real.log (500000 / 983073) ∧
    -Real.log (500000 / 983073) ≤ (338037641 / 500000000) := by
  have h := checkLog_sound (w := (483073 / 1483073)) (n := 12)
    (lo := (676075281 / 1000000000)) (hi := (338037641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983073 / 500000) = 1/(500000 / 983073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676075281 / 1000000000) (338037641 / 500000000) (Real.log (983073 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983073 / 500000) = -Real.log (500000 / 983073) := by
    rw [show ((983073 / 500000) : ℝ) = ((500000 / 983073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (677139623 / 200000000) ≤ -Real.log (16927 / 500000) ∧
    -Real.log (16927 / 500000) ≤ (84642453 / 25000000) := by
  have h := checkLog_sound (w := (14323 / 48177)) (n := 12)
    (lo := (122621879 / 200000000)) (hi := (153277349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16927) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16927) = 1/(16927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-84642453 / 25000000) (-677139623 / 200000000) (Real.log (16927 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676225309 / 1000000000) ≤ -Real.log (1000000 / 1966441) ∧
    -Real.log (1000000 / 1966441) ≤ (67622531 / 100000000) := by
  have h := checkLog_sound (w := (966441 / 2966441)) (n := 12)
    (lo := (676225309 / 1000000000)) (hi := (67622531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966441 / 1000000) = 1/(1000000 / 1966441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676225309 / 1000000000) (67622531 / 100000000) (Real.log (1966441 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1966441 / 1000000) = -Real.log (1000000 / 1966441) := by
    rw [show ((1966441 / 1000000) : ℝ) = ((1000000 / 1966441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (212153137 / 62500000) ≤ -Real.log (33559 / 1000000) ∧
    -Real.log (33559 / 1000000) ≤ (3394450197 / 1000000000) := by
  have h := checkLog_sound (w := (28941 / 96059)) (n := 12)
    (lo := (19433171 / 31250000)) (hi := (621861473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33559) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33559) = 1/(33559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3394450197 / 1000000000) (-212153137 / 62500000) (Real.log (33559 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4070887671 / 1000000000) ≤ -Real.log (250000000000 / 14652241297091) ∧
    -Real.log (250000000000 / 14652241297091) ≤ (4070887677 / 1000000000) := by
  have h := checkLog_sound (w := (6652241297091 / 22652241297091)) (n := 12)
    (lo := (605151771 / 1000000000)) (hi := (151287943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14652241297091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14652241297091 / 8000000000000) = 1/(250000000000 / 14652241297091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4070887671 / 1000000000) (4070887677 / 1000000000) (Real.log (14652241297091 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14652241297091 / 250000000000) = -Real.log (250000000000 / 14652241297091) := by
    rw [show ((14652241297091 / 250000000000) : ℝ) = ((250000000000 / 14652241297091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (509960679 / 125000000) ≤ -Real.log (250000000000 / 14781716922707) ∧
    -Real.log (250000000000 / 14781716922707) ≤ (2039842719 / 500000000) := by
  have h := checkLog_sound (w := (6781716922707 / 22781716922707)) (n := 12)
    (lo := (153487383 / 250000000)) (hi := (613949533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14781716922707 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14781716922707 / 8000000000000) = 1/(250000000000 / 14781716922707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (509960679 / 125000000) (2039842719 / 500000000) (Real.log (14781716922707 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14781716922707 / 250000000000) = -Real.log (250000000000 / 14781716922707) := by
    rw [show ((14781716922707 / 250000000000) : ℝ) = ((250000000000 / 14781716922707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1015443349 / 250000000) ≤ -Real.log (100000000000 / 5807721391859) ∧
    -Real.log (100000000000 / 5807721391859) ≤ (2030886701 / 500000000) := by
  have h := checkLog_sound (w := (2607721391859 / 9007721391859)) (n := 12)
    (lo := (74504687 / 125000000)) (hi := (596037497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5807721391859 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5807721391859 / 3200000000000) = 1/(100000000000 / 5807721391859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1015443349 / 250000000) (2030886701 / 500000000) (Real.log (5807721391859 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5807721391859 / 100000000000) = -Real.log (100000000000 / 5807721391859) := by
    rw [show ((5807721391859 / 100000000000) : ℝ) = ((100000000000 / 5807721391859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2035337751 / 500000000) ≤ -Real.log (250000000000 / 14649132870467) ∧
    -Real.log (250000000000 / 14649132870467) ≤ (1017668877 / 250000000) := by
  have h := checkLog_sound (w := (6649132870467 / 22649132870467)) (n := 12)
    (lo := (302469801 / 500000000)) (hi := (604939603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14649132870467 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14649132870467 / 8000000000000) = 1/(250000000000 / 14649132870467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2035337751 / 500000000) (1017668877 / 250000000) (Real.log (14649132870467 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14649132870467 / 250000000000) = -Real.log (250000000000 / 14649132870467) := by
    rw [show ((14649132870467 / 250000000000) : ℝ) = ((250000000000 / 14649132870467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0093

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0094Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0094
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

theorem reflection_log_1_neg : (168136449 / 250000000) ≤ -Real.log (6400 / 12539) ∧
    -Real.log (6400 / 12539) ≤ (672545797 / 1000000000) := by
  have h := checkLog_sound (w := (6139 / 18939)) (n := 12)
    (lo := (168136449 / 250000000)) (hi := (672545797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12539 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12539 / 6400) = 1/(6400 / 12539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (168136449 / 250000000) (672545797 / 1000000000) (Real.log (12539 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12539 / 6400) = -Real.log (6400 / 12539) := by
    rw [show ((12539 / 6400) : ℝ) = ((6400 / 12539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3199532859 / 1000000000) ≤ -Real.log (261 / 6400) ∧
    -Real.log (261 / 6400) ≤ (49992701 / 15625000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 261) = 1/(261 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49992701 / 15625000) (-3199532859 / 1000000000) (Real.log (261 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672356369 / 1000000000) ≤ -Real.log (51200 / 100293) ∧
    -Real.log (51200 / 100293) ≤ (67235637 / 100000000) := by
  have h := checkLog_sound (w := (49093 / 151493)) (n := 12)
    (lo := (672356369 / 1000000000)) (hi := (67235637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100293 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100293 / 51200) = 1/(51200 / 100293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672356369 / 1000000000) (67235637 / 100000000) (Real.log (100293 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100293 / 51200) = -Real.log (51200 / 100293) := by
    rw [show ((100293 / 51200) : ℝ) = ((51200 / 100293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1595237197 / 500000000) ≤ -Real.log (2107 / 51200) ∧
    -Real.log (2107 / 51200) ≤ (3190474399 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2107) = 1/(2107 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3190474399 / 1000000000) (-1595237197 / 500000000) (Real.log (2107 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (162877763 / 250000000) ≤ -Real.log (3200 / 6139) ∧
    -Real.log (3200 / 6139) ≤ (651511053 / 1000000000) := by
  have h := checkLog_sound (w := (2939 / 9339)) (n := 12)
    (lo := (162877763 / 250000000)) (hi := (651511053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6139 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6139 / 3200) = 1/(3200 / 6139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (162877763 / 250000000) (651511053 / 1000000000) (Real.log (6139 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6139 / 3200) = -Real.log (3200 / 6139) := by
    rw [show ((6139 / 3200) : ℝ) = ((3200 / 6139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2506385679 / 1000000000) ≤ -Real.log (261 / 3200) ∧
    -Real.log (261 / 3200) ≤ (2506385683 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 261) = 1/(261 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2506385683 / 1000000000) (-2506385679 / 1000000000) (Real.log (261 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (325562053 / 500000000) ≤ -Real.log (25600 / 49093) ∧
    -Real.log (25600 / 49093) ≤ (651124107 / 1000000000) := by
  have h := checkLog_sound (w := (23493 / 74693)) (n := 12)
    (lo := (325562053 / 500000000)) (hi := (651124107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49093 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49093 / 25600) = 1/(25600 / 49093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (325562053 / 500000000) (651124107 / 1000000000) (Real.log (49093 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49093 / 25600) = -Real.log (25600 / 49093) := by
    rw [show ((49093 / 25600) : ℝ) = ((25600 / 49093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1248663607 / 500000000) ≤ -Real.log (2107 / 25600) ∧
    -Real.log (2107 / 25600) ≤ (1248663609 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2107) = 1/(2107 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1248663609 / 500000000) (-1248663607 / 500000000) (Real.log (2107 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67608291 / 100000000) ≤ -Real.log (1000000 / 1966161) ∧
    -Real.log (1000000 / 1966161) ≤ (676082911 / 1000000000) := by
  have h := checkLog_sound (w := (966161 / 2966161)) (n := 12)
    (lo := (67608291 / 100000000)) (hi := (676082911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966161 / 1000000) = 1/(1000000 / 1966161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67608291 / 100000000) (676082911 / 1000000000) (Real.log (1966161 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1966161 / 1000000) = -Real.log (1000000 / 1966161) := by
    rw [show ((1966161 / 1000000) : ℝ) = ((1000000 / 1966161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3386141293 / 1000000000) ≤ -Real.log (33839 / 1000000) ∧
    -Real.log (33839 / 1000000) ≤ (1693070649 / 500000000) := by
  have h := checkLog_sound (w := (28661 / 96339)) (n := 12)
    (lo := (613552573 / 1000000000)) (hi := (306776287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33839) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33839) = 1/(33839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1693070649 / 500000000) (-3386141293 / 1000000000) (Real.log (33839 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (338114689 / 500000000) ≤ -Real.log (1000000 / 1966449) ∧
    -Real.log (1000000 / 1966449) ≤ (676229379 / 1000000000) := by
  have h := checkLog_sound (w := (966449 / 2966449)) (n := 12)
    (lo := (338114689 / 500000000)) (hi := (676229379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966449 / 1000000) = 1/(1000000 / 1966449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (338114689 / 500000000) (676229379 / 1000000000) (Real.log (1966449 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1966449 / 1000000) = -Real.log (1000000 / 1966449) := by
    rw [show ((1966449 / 1000000) : ℝ) = ((1000000 / 1966449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3394688607 / 1000000000) ≤ -Real.log (33551 / 1000000) ∧
    -Real.log (33551 / 1000000) ≤ (848672153 / 250000000) := by
  have h := checkLog_sound (w := (28949 / 96051)) (n := 12)
    (lo := (622099887 / 1000000000)) (hi := (38881243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33551) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33551) = 1/(33551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-848672153 / 250000000) (-3394688607 / 1000000000) (Real.log (33551 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675925739 / 1000000000) ≤ -Real.log (250000 / 491463) ∧
    -Real.log (250000 / 491463) ≤ (33796287 / 50000000) := by
  have h := checkLog_sound (w := (241463 / 741463)) (n := 12)
    (lo := (675925739 / 1000000000)) (hi := (33796287 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491463 / 250000) = 1/(250000 / 491463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675925739 / 1000000000) (33796287 / 50000000) (Real.log (491463 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (491463 / 250000) = -Real.log (250000 / 491463) := by
    rw [show ((491463 / 250000) : ℝ) = ((250000 / 491463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3377051257 / 1000000000) ≤ -Real.log (8537 / 250000) ∧
    -Real.log (8537 / 250000) ≤ (1688525631 / 500000000) := by
  have h := checkLog_sound (w := (3544 / 12081)) (n := 12)
    (lo := (604462537 / 1000000000)) (hi := (302231269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8537) = 1/(8537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1688525631 / 500000000) (-3377051257 / 1000000000) (Real.log (8537 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67607579 / 100000000) ≤ -Real.log (1000000 / 1966147) ∧
    -Real.log (1000000 / 1966147) ≤ (676075791 / 1000000000) := by
  have h := checkLog_sound (w := (966147 / 2966147)) (n := 12)
    (lo := (67607579 / 100000000)) (hi := (676075791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966147 / 1000000) = 1/(1000000 / 1966147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67607579 / 100000000) (676075791 / 1000000000) (Real.log (1966147 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1966147 / 1000000) = -Real.log (1000000 / 1966147) := by
    rw [show ((1966147 / 1000000) : ℝ) = ((1000000 / 1966147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (677145531 / 200000000) ≤ -Real.log (33853 / 1000000) ∧
    -Real.log (33853 / 1000000) ≤ (169286383 / 50000000) := by
  have h := checkLog_sound (w := (28647 / 96353)) (n := 12)
    (lo := (122627787 / 200000000)) (hi := (76642367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33853) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33853) = 1/(33853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-169286383 / 50000000) (-677145531 / 200000000) (Real.log (33853 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4062224203 / 1000000000) ≤ -Real.log (4000000000 / 232413605603) ∧
    -Real.log (4000000000 / 232413605603) ≤ (4062224209 / 1000000000) := by
  have h := checkLog_sound (w := (104413605603 / 360413605603)) (n := 12)
    (lo := (596488303 / 1000000000)) (hi := (37280519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232413605603 / 128000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(232413605603 / 128000000000) = 1/(4000000000 / 232413605603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4062224203 / 1000000000) (4062224209 / 1000000000) (Real.log (232413605603 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (232413605603 / 4000000000) = -Real.log (4000000000 / 232413605603) := by
    rw [show ((232413605603 / 4000000000) : ℝ) = ((4000000000 / 232413605603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (814183597 / 200000000) ≤ -Real.log (250000000000 / 14652685463921) ∧
    -Real.log (250000000000 / 14652685463921) ≤ (4070917991 / 1000000000) := by
  have h := checkLog_sound (w := (6652685463921 / 22652685463921)) (n := 12)
    (lo := (121036417 / 200000000)) (hi := (302591043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14652685463921 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14652685463921 / 8000000000000) = 1/(250000000000 / 14652685463921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (814183597 / 200000000) (4070917991 / 1000000000) (Real.log (14652685463921 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14652685463921 / 250000000000) = -Real.log (250000000000 / 14652685463921) := by
    rw [show ((14652685463921 / 250000000000) : ℝ) = ((250000000000 / 14652685463921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1013244249 / 250000000) ≤ -Real.log (500000000000 / 28784291905821) ∧
    -Real.log (500000000000 / 28784291905821) ≤ (2026488501 / 500000000) := by
  have h := checkLog_sound (w := (12784291905821 / 44784291905821)) (n := 12)
    (lo := (73405137 / 125000000)) (hi := (587241097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28784291905821 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28784291905821 / 16000000000000) = 1/(500000000000 / 28784291905821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1013244249 / 250000000) (2026488501 / 500000000) (Real.log (28784291905821 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28784291905821 / 500000000000) = -Real.log (500000000000 / 28784291905821) := by
    rw [show ((28784291905821 / 500000000000) : ℝ) = ((500000000000 / 28784291905821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1015450861 / 250000000) ≤ -Real.log (500000000000 / 29039479514371) ∧
    -Real.log (500000000000 / 29039479514371) ≤ (81236069 / 20000000) := by
  have h := checkLog_sound (w := (13039479514371 / 45039479514371)) (n := 12)
    (lo := (74508443 / 125000000)) (hi := (119213509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29039479514371 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29039479514371 / 16000000000000) = 1/(500000000000 / 29039479514371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1015450861 / 250000000) (81236069 / 20000000) (Real.log (29039479514371 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (29039479514371 / 500000000000) = -Real.log (500000000000 / 29039479514371) := by
    rw [show ((29039479514371 / 500000000000) : ℝ) = ((500000000000 / 29039479514371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0094

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0095Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0095
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

theorem reflection_log_1_neg : (672356369 / 1000000000) ≤ -Real.log (51200 / 100293) ∧
    -Real.log (51200 / 100293) ≤ (67235637 / 100000000) := by
  have h := checkLog_sound (w := (49093 / 151493)) (n := 12)
    (lo := (672356369 / 1000000000)) (hi := (67235637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100293 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100293 / 51200) = 1/(51200 / 100293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672356369 / 1000000000) (67235637 / 100000000) (Real.log (100293 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100293 / 51200) = -Real.log (51200 / 100293) := by
    rw [show ((100293 / 51200) : ℝ) = ((51200 / 100293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1595237197 / 500000000) ≤ -Real.log (2107 / 51200) ∧
    -Real.log (2107 / 51200) ≤ (3190474399 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2107) = 1/(2107 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3190474399 / 1000000000) (-1595237197 / 500000000) (Real.log (2107 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336083453 / 500000000) ≤ -Real.log (25600 / 50137) ∧
    -Real.log (25600 / 50137) ≤ (672166907 / 1000000000) := by
  have h := checkLog_sound (w := (24537 / 75737)) (n := 12)
    (lo := (336083453 / 500000000)) (hi := (672166907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50137 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50137 / 25600) = 1/(25600 / 50137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336083453 / 500000000) (672166907 / 1000000000) (Real.log (50137 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50137 / 25600) = -Real.log (25600 / 50137) := by
    rw [show ((50137 / 25600) : ℝ) = ((25600 / 50137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3181497249 / 1000000000) ≤ -Real.log (1063 / 25600) ∧
    -Real.log (1063 / 25600) ≤ (1590748627 / 500000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1063) = 1/(1063 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1590748627 / 500000000) (-3181497249 / 1000000000) (Real.log (1063 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (325562053 / 500000000) ≤ -Real.log (25600 / 49093) ∧
    -Real.log (25600 / 49093) ≤ (651124107 / 1000000000) := by
  have h := checkLog_sound (w := (23493 / 74693)) (n := 12)
    (lo := (325562053 / 500000000)) (hi := (651124107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49093 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49093 / 25600) = 1/(25600 / 49093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (325562053 / 500000000) (651124107 / 1000000000) (Real.log (49093 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49093 / 25600) = -Real.log (25600 / 49093) := by
    rw [show ((49093 / 25600) : ℝ) = ((25600 / 49093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1248663607 / 500000000) ≤ -Real.log (2107 / 25600) ∧
    -Real.log (2107 / 25600) ≤ (1248663609 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2107) = 1/(2107 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1248663609 / 500000000) (-1248663607 / 500000000) (Real.log (2107 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (650737011 / 1000000000) ≤ -Real.log (12800 / 24537) ∧
    -Real.log (12800 / 24537) ≤ (162684253 / 250000000) := by
  have h := checkLog_sound (w := (11737 / 37337)) (n := 12)
    (lo := (650737011 / 1000000000)) (hi := (162684253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24537 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24537 / 12800) = 1/(12800 / 24537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (650737011 / 1000000000) (162684253 / 250000000) (Real.log (24537 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24537 / 12800) = -Real.log (12800 / 24537) := by
    rw [show ((24537 / 12800) : ℝ) = ((12800 / 24537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2488350069 / 1000000000) ≤ -Real.log (1063 / 12800) ∧
    -Real.log (1063 / 12800) ≤ (2488350073 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1063) = 1/(1063 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2488350073 / 1000000000) (-2488350069 / 1000000000) (Real.log (1063 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675936421 / 1000000000) ≤ -Real.log (1000000 / 1965873) ∧
    -Real.log (1000000 / 1965873) ≤ (337968211 / 500000000) := by
  have h := checkLog_sound (w := (965873 / 2965873)) (n := 12)
    (lo := (675936421 / 1000000000)) (hi := (337968211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965873 / 1000000) = 1/(1000000 / 1965873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675936421 / 1000000000) (337968211 / 500000000) (Real.log (1965873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1965873 / 1000000) = -Real.log (1000000 / 1965873) := by
    rw [show ((1965873 / 1000000) : ℝ) = ((1000000 / 1965873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (211104151 / 62500000) ≤ -Real.log (34127 / 1000000) ∧
    -Real.log (34127 / 1000000) ≤ (3377666421 / 1000000000) := by
  have h := checkLog_sound (w := (28373 / 96627)) (n := 12)
    (lo := (9454339 / 15625000)) (hi := (605077697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34127) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34127) = 1/(34127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3377666421 / 1000000000) (-211104151 / 62500000) (Real.log (34127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676083419 / 1000000000) ≤ -Real.log (500000 / 983081) ∧
    -Real.log (500000 / 983081) ≤ (33804171 / 50000000) := by
  have h := checkLog_sound (w := (483081 / 1483081)) (n := 12)
    (lo := (676083419 / 1000000000)) (hi := (33804171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983081 / 500000) = 1/(500000 / 983081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676083419 / 1000000000) (33804171 / 50000000) (Real.log (983081 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983081 / 500000) = -Real.log (500000 / 983081) := by
    rw [show ((983081 / 500000) : ℝ) = ((500000 / 983081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (677234169 / 200000000) ≤ -Real.log (16919 / 500000) ∧
    -Real.log (16919 / 500000) ≤ (67723417 / 20000000) := by
  have h := checkLog_sound (w := (14331 / 48169)) (n := 12)
    (lo := (4908657 / 8000000)) (hi := (306791063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16919) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16919) = 1/(16919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67723417 / 20000000) (-677234169 / 200000000) (Real.log (16919 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337888087 / 500000000) ≤ -Real.log (500000 / 982779) ∧
    -Real.log (500000 / 982779) ≤ (27031047 / 40000000) := by
  have h := checkLog_sound (w := (482779 / 1482779)) (n := 12)
    (lo := (337888087 / 500000000)) (hi := (27031047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982779 / 500000) = 1/(500000 / 982779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337888087 / 500000000) (27031047 / 40000000) (Real.log (982779 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (982779 / 500000) = -Real.log (500000 / 982779) := by
    rw [show ((982779 / 500000) : ℝ) = ((500000 / 982779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1684239263 / 500000000) ≤ -Real.log (17221 / 500000) ∧
    -Real.log (17221 / 500000) ≤ (3368478531 / 1000000000) := by
  have h := checkLog_sound (w := (14029 / 48471)) (n := 12)
    (lo := (297944903 / 500000000)) (hi := (595889807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17221) = 1/(17221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3368478531 / 1000000000) (-1684239263 / 500000000) (Real.log (17221 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675926247 / 1000000000) ≤ -Real.log (1000000 / 1965853) ∧
    -Real.log (1000000 / 1965853) ≤ (84490781 / 125000000) := by
  have h := checkLog_sound (w := (965853 / 2965853)) (n := 12)
    (lo := (675926247 / 1000000000)) (hi := (84490781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965853 / 1000000) = 1/(1000000 / 1965853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675926247 / 1000000000) (84490781 / 125000000) (Real.log (1965853 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1965853 / 1000000) = -Real.log (1000000 / 1965853) := by
    rw [show ((1965853 / 1000000) : ℝ) = ((1000000 / 1965853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1688540271 / 500000000) ≤ -Real.log (34147 / 1000000) ∧
    -Real.log (34147 / 1000000) ≤ (3377080547 / 1000000000) := by
  have h := checkLog_sound (w := (28353 / 96647)) (n := 12)
    (lo := (302245911 / 500000000)) (hi := (604491823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34147) = 1/(34147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3377080547 / 1000000000) (-1688540271 / 500000000) (Real.log (34147 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4053602837 / 1000000000) ≤ -Real.log (500000000000 / 28802311952413) ∧
    -Real.log (500000000000 / 28802311952413) ≤ (4053602843 / 1000000000) := by
  have h := checkLog_sound (w := (12802311952413 / 44802311952413)) (n := 12)
    (lo := (587866937 / 1000000000)) (hi := (293933469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28802311952413 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28802311952413 / 16000000000000) = 1/(500000000000 / 28802311952413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4053602837 / 1000000000) (4053602843 / 1000000000) (Real.log (28802311952413 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28802311952413 / 500000000000) = -Real.log (500000000000 / 28802311952413) := by
    rw [show ((28802311952413 / 500000000000) : ℝ) = ((500000000000 / 28802311952413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4062254263 / 1000000000) ≤ -Real.log (250000000000 / 14526287014599) ∧
    -Real.log (250000000000 / 14526287014599) ≤ (4062254269 / 1000000000) := by
  have h := checkLog_sound (w := (6526287014599 / 22526287014599)) (n := 12)
    (lo := (596518363 / 1000000000)) (hi := (149129591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14526287014599 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14526287014599 / 8000000000000) = 1/(250000000000 / 14526287014599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4062254263 / 1000000000) (4062254269 / 1000000000) (Real.log (14526287014599 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14526287014599 / 250000000000) = -Real.log (250000000000 / 14526287014599) := by
    rw [show ((14526287014599 / 250000000000) : ℝ) = ((250000000000 / 14526287014599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40442547 / 10000000) ≤ -Real.log (500000000000 / 28534318564543) ∧
    -Real.log (500000000000 / 28534318564543) ≤ (2022127353 / 500000000) := by
  have h := checkLog_sound (w := (12534318564543 / 44534318564543)) (n := 12)
    (lo := (1446297 / 2500000)) (hi := (578518801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28534318564543 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28534318564543 / 16000000000000) = 1/(500000000000 / 28534318564543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (40442547 / 10000000) (2022127353 / 500000000) (Real.log (28534318564543 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28534318564543 / 500000000000) = -Real.log (500000000000 / 28534318564543) := by
    rw [show ((28534318564543 / 500000000000) : ℝ) = ((500000000000 / 28534318564543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4053006789 / 1000000000) ≤ -Real.log (500000000000 / 28785149500689) ∧
    -Real.log (500000000000 / 28785149500689) ≤ (810601359 / 200000000) := by
  have h := checkLog_sound (w := (12785149500689 / 44785149500689)) (n := 12)
    (lo := (587270889 / 1000000000)) (hi := (58727089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28785149500689 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28785149500689 / 16000000000000) = 1/(500000000000 / 28785149500689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4053006789 / 1000000000) (810601359 / 200000000) (Real.log (28785149500689 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28785149500689 / 500000000000) = -Real.log (500000000000 / 28785149500689) := by
    rw [show ((28785149500689 / 500000000000) : ℝ) = ((500000000000 / 28785149500689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0095

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0096Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0096
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

theorem reflection_log_1_neg : (336083453 / 500000000) ≤ -Real.log (25600 / 50137) ∧
    -Real.log (25600 / 50137) ≤ (672166907 / 1000000000) := by
  have h := checkLog_sound (w := (24537 / 75737)) (n := 12)
    (lo := (336083453 / 500000000)) (hi := (672166907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50137 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50137 / 25600) = 1/(25600 / 50137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336083453 / 500000000) (672166907 / 1000000000) (Real.log (50137 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50137 / 25600) = -Real.log (25600 / 50137) := by
    rw [show ((50137 / 25600) : ℝ) = ((25600 / 50137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3181497249 / 1000000000) ≤ -Real.log (1063 / 25600) ∧
    -Real.log (1063 / 25600) ≤ (1590748627 / 500000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1063) = 1/(1063 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1590748627 / 500000000) (-3181497249 / 1000000000) (Real.log (1063 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10499647 / 15625000) ≤ -Real.log (10240 / 20051) ∧
    -Real.log (10240 / 20051) ≤ (671977409 / 1000000000) := by
  have h := checkLog_sound (w := (9811 / 30291)) (n := 12)
    (lo := (10499647 / 15625000)) (hi := (671977409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20051 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20051 / 10240) = 1/(10240 / 20051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10499647 / 15625000) (671977409 / 1000000000) (Real.log (20051 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20051 / 10240) = -Real.log (10240 / 20051) := by
    rw [show ((20051 / 10240) : ℝ) = ((10240 / 20051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3172599977 / 1000000000) ≤ -Real.log (429 / 10240) ∧
    -Real.log (429 / 10240) ≤ (1586299991 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 429) = 1/(429 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1586299991 / 500000000) (-3172599977 / 1000000000) (Real.log (429 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (650737011 / 1000000000) ≤ -Real.log (12800 / 24537) ∧
    -Real.log (12800 / 24537) ≤ (162684253 / 250000000) := by
  have h := checkLog_sound (w := (11737 / 37337)) (n := 12)
    (lo := (650737011 / 1000000000)) (hi := (162684253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24537 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24537 / 12800) = 1/(12800 / 24537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (650737011 / 1000000000) (162684253 / 250000000) (Real.log (24537 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24537 / 12800) = -Real.log (12800 / 24537) := by
    rw [show ((24537 / 12800) : ℝ) = ((12800 / 24537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2488350069 / 1000000000) ≤ -Real.log (1063 / 12800) ∧
    -Real.log (1063 / 12800) ≤ (2488350073 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1063) = 1/(1063 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2488350073 / 1000000000) (-2488350069 / 1000000000) (Real.log (1063 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (325174883 / 500000000) ≤ -Real.log (5120 / 9811) ∧
    -Real.log (5120 / 9811) ≤ (650349767 / 1000000000) := by
  have h := checkLog_sound (w := (4691 / 14931)) (n := 12)
    (lo := (325174883 / 500000000)) (hi := (650349767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9811 / 5120) = 1/(5120 / 9811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (325174883 / 500000000) (650349767 / 1000000000) (Real.log (9811 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9811 / 5120) = -Real.log (5120 / 9811) := by
    rw [show ((9811 / 5120) : ℝ) = ((5120 / 9811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2479452797 / 1000000000) ≤ -Real.log (429 / 5120) ∧
    -Real.log (429 / 5120) ≤ (2479452801 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 429) = 1/(429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2479452801 / 1000000000) (-2479452797 / 1000000000) (Real.log (429 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675790419 / 1000000000) ≤ -Real.log (500000 / 982793) ∧
    -Real.log (500000 / 982793) ≤ (33789521 / 50000000) := by
  have h := checkLog_sound (w := (482793 / 1482793)) (n := 12)
    (lo := (675790419 / 1000000000)) (hi := (33789521 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982793 / 500000) = 1/(500000 / 982793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675790419 / 1000000000) (33789521 / 50000000) (Real.log (982793 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (982793 / 500000) = -Real.log (500000 / 982793) := by
    rw [show ((982793 / 500000) : ℝ) = ((500000 / 982793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1684645909 / 500000000) ≤ -Real.log (17207 / 500000) ∧
    -Real.log (17207 / 500000) ≤ (3369291823 / 1000000000) := by
  have h := checkLog_sound (w := (14043 / 48457)) (n := 12)
    (lo := (298351549 / 500000000)) (hi := (596703099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17207) = 1/(17207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3369291823 / 1000000000) (-1684645909 / 500000000) (Real.log (17207 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67593693 / 100000000) ≤ -Real.log (500000 / 982937) ∧
    -Real.log (500000 / 982937) ≤ (675936931 / 1000000000) := by
  have h := checkLog_sound (w := (482937 / 1482937)) (n := 12)
    (lo := (67593693 / 100000000)) (hi := (675936931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982937 / 500000) = 1/(500000 / 982937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67593693 / 100000000) (675936931 / 1000000000) (Real.log (982937 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (982937 / 500000) = -Real.log (500000 / 982937) := by
    rw [show ((982937 / 500000) : ℝ) = ((500000 / 982937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3377695719 / 1000000000) ≤ -Real.log (17063 / 500000) ∧
    -Real.log (17063 / 500000) ≤ (844423931 / 250000000) := by
  have h := checkLog_sound (w := (14187 / 48313)) (n := 12)
    (lo := (605106999 / 1000000000)) (hi := (605107 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17063) = 1/(17063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-844423931 / 250000000) (-3377695719 / 1000000000) (Real.log (17063 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675626587 / 1000000000) ≤ -Real.log (62500 / 122829) ∧
    -Real.log (62500 / 122829) ≤ (168906647 / 250000000) := by
  have h := checkLog_sound (w := (60329 / 185329)) (n := 12)
    (lo := (675626587 / 1000000000)) (hi := (168906647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122829 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122829 / 62500) = 1/(62500 / 122829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675626587 / 1000000000) (168906647 / 250000000) (Real.log (122829 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (122829 / 62500) = -Real.log (62500 / 122829) := by
    rw [show ((122829 / 62500) : ℝ) = ((62500 / 122829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3359978663 / 1000000000) ≤ -Real.log (2171 / 62500) ∧
    -Real.log (2171 / 62500) ≤ (839994667 / 250000000) := by
  have h := checkLog_sound (w := (6941 / 24309)) (n := 12)
    (lo := (587389943 / 1000000000)) (hi := (73423743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8684) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8684) = 1/(2171 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-839994667 / 250000000) (-3359978663 / 1000000000) (Real.log (2171 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675776683 / 1000000000) ≤ -Real.log (1000000 / 1965559) ∧
    -Real.log (1000000 / 1965559) ≤ (168944171 / 250000000) := by
  have h := checkLog_sound (w := (965559 / 2965559)) (n := 12)
    (lo := (675776683 / 1000000000)) (hi := (168944171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965559 / 1000000) = 1/(1000000 / 1965559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675776683 / 1000000000) (168944171 / 250000000) (Real.log (1965559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1965559 / 1000000) = -Real.log (1000000 / 1965559) := by
    rw [show ((1965559 / 1000000) : ℝ) = ((1000000 / 1965559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3368507561 / 1000000000) ≤ -Real.log (34441 / 1000000) ∧
    -Real.log (34441 / 1000000) ≤ (1684253783 / 500000000) := by
  have h := checkLog_sound (w := (28059 / 96941)) (n := 12)
    (lo := (595918841 / 1000000000)) (hi := (297959421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34441) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34441) = 1/(34441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1684253783 / 500000000) (-3368507561 / 1000000000) (Real.log (34441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4045082237 / 1000000000) ≤ -Real.log (500000000000 / 28557941535421) ∧
    -Real.log (500000000000 / 28557941535421) ≤ (4045082243 / 1000000000) := by
  have h := checkLog_sound (w := (12557941535421 / 44557941535421)) (n := 12)
    (lo := (579346337 / 1000000000)) (hi := (289673169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28557941535421 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28557941535421 / 16000000000000) = 1/(500000000000 / 28557941535421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4045082237 / 1000000000) (4045082243 / 1000000000) (Real.log (28557941535421 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28557941535421 / 500000000000) = -Real.log (500000000000 / 28557941535421) := by
    rw [show ((28557941535421 / 500000000000) : ℝ) = ((500000000000 / 28557941535421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4053632649 / 1000000000) ≤ -Real.log (25000000000 / 1440158530153) ∧
    -Real.log (25000000000 / 1440158530153) ≤ (810726531 / 200000000) := by
  have h := checkLog_sound (w := (640158530153 / 2240158530153)) (n := 12)
    (lo := (587896749 / 1000000000)) (hi := (2351587 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1440158530153 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1440158530153 / 800000000000) = 1/(25000000000 / 1440158530153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4053632649 / 1000000000) (810726531 / 200000000) (Real.log (1440158530153 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1440158530153 / 25000000000) = -Real.log (25000000000 / 1440158530153) := by
    rw [show ((1440158530153 / 25000000000) : ℝ) = ((25000000000 / 1440158530153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16142421 / 4000000) ≤ -Real.log (15625000000 / 884018021649) ∧
    -Real.log (15625000000 / 884018021649) ≤ (504450657 / 125000000) := by
  have h := checkLog_sound (w := (384018021649 / 1384018021649)) (n := 12)
    (lo := (11397387 / 20000000)) (hi := (569869351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884018021649 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(884018021649 / 500000000000) = 1/(15625000000 / 884018021649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16142421 / 4000000) (504450657 / 125000000) (Real.log (884018021649 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (884018021649 / 15625000000) = -Real.log (15625000000 / 884018021649) := by
    rw [show ((884018021649 / 15625000000) : ℝ) = ((15625000000 / 884018021649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1011071061 / 250000000) ≤ -Real.log (20000000000 / 1141406463227) ∧
    -Real.log (20000000000 / 1141406463227) ≤ (16177137 / 4000000) := by
  have h := checkLog_sound (w := (501406463227 / 1781406463227)) (n := 12)
    (lo := (72318543 / 125000000)) (hi := (115709669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141406463227 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1141406463227 / 640000000000) = 1/(20000000000 / 1141406463227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1011071061 / 250000000) (16177137 / 4000000) (Real.log (1141406463227 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1141406463227 / 20000000000) = -Real.log (20000000000 / 1141406463227) := by
    rw [show ((1141406463227 / 20000000000) : ℝ) = ((20000000000 / 1141406463227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0096

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0097Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0097
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

theorem reflection_log_1_neg : (10499647 / 15625000) ≤ -Real.log (10240 / 20051) ∧
    -Real.log (10240 / 20051) ≤ (671977409 / 1000000000) := by
  have h := checkLog_sound (w := (9811 / 30291)) (n := 12)
    (lo := (10499647 / 15625000)) (hi := (671977409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20051 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20051 / 10240) = 1/(10240 / 20051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10499647 / 15625000) (671977409 / 1000000000) (Real.log (20051 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20051 / 10240) = -Real.log (10240 / 20051) := by
    rw [show ((20051 / 10240) : ℝ) = ((10240 / 20051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3172599977 / 1000000000) ≤ -Real.log (429 / 10240) ∧
    -Real.log (429 / 10240) ≤ (1586299991 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 429) = 1/(429 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1586299991 / 500000000) (-3172599977 / 1000000000) (Real.log (429 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (671787873 / 1000000000) ≤ -Real.log (12800 / 25059) ∧
    -Real.log (12800 / 25059) ≤ (335893937 / 500000000) := by
  have h := checkLog_sound (w := (12259 / 37859)) (n := 12)
    (lo := (671787873 / 1000000000)) (hi := (335893937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25059 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25059 / 12800) = 1/(12800 / 25059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (671787873 / 1000000000) (335893937 / 500000000) (Real.log (25059 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25059 / 12800) = -Real.log (12800 / 25059) := by
    rw [show ((25059 / 12800) : ℝ) = ((12800 / 25059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197736323 / 62500000) ≤ -Real.log (541 / 12800) ∧
    -Real.log (541 / 12800) ≤ (3163781173 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 541) = 1/(541 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3163781173 / 1000000000) (-197736323 / 62500000) (Real.log (541 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (325174883 / 500000000) ≤ -Real.log (5120 / 9811) ∧
    -Real.log (5120 / 9811) ≤ (650349767 / 1000000000) := by
  have h := checkLog_sound (w := (4691 / 14931)) (n := 12)
    (lo := (325174883 / 500000000)) (hi := (650349767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9811 / 5120) = 1/(5120 / 9811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (325174883 / 500000000) (650349767 / 1000000000) (Real.log (9811 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9811 / 5120) = -Real.log (5120 / 9811) := by
    rw [show ((9811 / 5120) : ℝ) = ((5120 / 9811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2479452797 / 1000000000) ≤ -Real.log (429 / 5120) ∧
    -Real.log (429 / 5120) ≤ (2479452801 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 429) = 1/(429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2479452801 / 1000000000) (-2479452797 / 1000000000) (Real.log (429 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (64996237 / 100000000) ≤ -Real.log (6400 / 12259) ∧
    -Real.log (6400 / 12259) ≤ (649962371 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 18659)) (n := 12)
    (lo := (64996237 / 100000000)) (hi := (649962371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12259 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12259 / 6400) = 1/(6400 / 12259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (64996237 / 100000000) (649962371 / 1000000000) (Real.log (12259 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12259 / 6400) = -Real.log (6400 / 12259) := by
    rw [show ((12259 / 6400) : ℝ) = ((6400 / 12259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617658497 / 250000000) ≤ -Real.log (541 / 6400) ∧
    -Real.log (541 / 6400) ≤ (308829249 / 125000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 541) = 1/(541 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-308829249 / 125000000) (-617658497 / 250000000) (Real.log (541 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168911099 / 250000000) ≤ -Real.log (1000000 / 1965299) ∧
    -Real.log (1000000 / 1965299) ≤ (675644397 / 1000000000) := by
  have h := checkLog_sound (w := (965299 / 2965299)) (n := 12)
    (lo := (168911099 / 250000000)) (hi := (675644397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965299 / 1000000) = 1/(1000000 / 1965299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168911099 / 250000000) (675644397 / 1000000000) (Real.log (1965299 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1965299 / 1000000) = -Real.log (1000000 / 1965299) := by
    rw [show ((1965299 / 1000000) : ℝ) = ((1000000 / 1965299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3360986771 / 1000000000) ≤ -Real.log (34701 / 1000000) ∧
    -Real.log (34701 / 1000000) ≤ (420123347 / 125000000) := by
  have h := checkLog_sound (w := (27799 / 97201)) (n := 12)
    (lo := (588398051 / 1000000000)) (hi := (147099513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34701) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34701) = 1/(34701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-420123347 / 125000000) (-3360986771 / 1000000000) (Real.log (34701 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42236933 / 62500000) ≤ -Real.log (1000000 / 1965587) ∧
    -Real.log (1000000 / 1965587) ≤ (675790929 / 1000000000) := by
  have h := checkLog_sound (w := (965587 / 2965587)) (n := 12)
    (lo := (42236933 / 62500000)) (hi := (675790929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965587 / 1000000) = 1/(1000000 / 1965587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42236933 / 62500000) (675790929 / 1000000000) (Real.log (1965587 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1965587 / 1000000) = -Real.log (1000000 / 1965587) := by
    rw [show ((1965587 / 1000000) : ℝ) = ((1000000 / 1965587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (842330219 / 250000000) ≤ -Real.log (34413 / 1000000) ∧
    -Real.log (34413 / 1000000) ≤ (3369320881 / 1000000000) := by
  have h := checkLog_sound (w := (28087 / 96913)) (n := 12)
    (lo := (149183039 / 250000000)) (hi := (596732157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34413) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34413) = 1/(34413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3369320881 / 1000000000) (-842330219 / 250000000) (Real.log (34413 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337738743 / 500000000) ≤ -Real.log (1000000 / 1964971) ∧
    -Real.log (1000000 / 1964971) ≤ (675477487 / 1000000000) := by
  have h := checkLog_sound (w := (964971 / 2964971)) (n := 12)
    (lo := (337738743 / 500000000)) (hi := (675477487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964971 / 1000000) = 1/(1000000 / 1964971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337738743 / 500000000) (675477487 / 1000000000) (Real.log (1964971 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964971 / 1000000) = -Real.log (1000000 / 1964971) := by
    rw [show ((1964971 / 1000000) : ℝ) = ((1000000 / 1964971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1675789493 / 500000000) ≤ -Real.log (35029 / 1000000) ∧
    -Real.log (35029 / 1000000) ≤ (3351578991 / 1000000000) := by
  have h := checkLog_sound (w := (27471 / 97529)) (n := 12)
    (lo := (289495133 / 500000000)) (hi := (578990267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35029) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35029) = 1/(35029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3351578991 / 1000000000) (-1675789493 / 500000000) (Real.log (35029 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84453387 / 125000000) ≤ -Real.log (200000 / 393053) ∧
    -Real.log (200000 / 393053) ≤ (675627097 / 1000000000) := by
  have h := checkLog_sound (w := (193053 / 593053)) (n := 12)
    (lo := (84453387 / 125000000)) (hi := (675627097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393053 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393053 / 200000) = 1/(200000 / 393053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84453387 / 125000000) (675627097 / 1000000000) (Real.log (393053 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393053 / 200000) = -Real.log (200000 / 393053) := by
    rw [show ((393053 / 200000) : ℝ) = ((200000 / 393053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (840001863 / 250000000) ≤ -Real.log (6947 / 200000) ∧
    -Real.log (6947 / 200000) ≤ (3360007457 / 1000000000) := by
  have h := checkLog_sound (w := (5553 / 19447)) (n := 12)
    (lo := (146854683 / 250000000)) (hi := (587418733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6947) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6947) = 1/(6947 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3360007457 / 1000000000) (-840001863 / 250000000) (Real.log (6947 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4036631167 / 1000000000) ≤ -Real.log (31250000000 / 1769850832829) ∧
    -Real.log (31250000000 / 1769850832829) ≤ (4036631173 / 1000000000) := by
  have h := checkLog_sound (w := (769850832829 / 2769850832829)) (n := 12)
    (lo := (570895267 / 1000000000)) (hi := (142723817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1769850832829 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1769850832829 / 1000000000000) = 1/(31250000000 / 1769850832829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4036631167 / 1000000000) (4036631173 / 1000000000) (Real.log (1769850832829 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1769850832829 / 31250000000) = -Real.log (31250000000 / 1769850832829) := by
    rw [show ((1769850832829 / 31250000000) : ℝ) = ((31250000000 / 1769850832829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1011277951 / 250000000) ≤ -Real.log (20000000000 / 1142351436957) ∧
    -Real.log (20000000000 / 1142351436957) ≤ (404511181 / 100000000) := by
  have h := checkLog_sound (w := (502351436957 / 1782351436957)) (n := 12)
    (lo := (18105497 / 31250000)) (hi := (115875181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142351436957 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1142351436957 / 640000000000) = 1/(20000000000 / 1142351436957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1011277951 / 250000000) (404511181 / 100000000) (Real.log (1142351436957 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1142351436957 / 20000000000) = -Real.log (20000000000 / 1142351436957) := by
    rw [show ((1142351436957 / 20000000000) : ℝ) = ((20000000000 / 1142351436957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4027056473 / 1000000000) ≤ -Real.log (250000000000 / 14023887350481) ∧
    -Real.log (250000000000 / 14023887350481) ≤ (4027056479 / 1000000000) := by
  have h := checkLog_sound (w := (6023887350481 / 22023887350481)) (n := 12)
    (lo := (561320573 / 1000000000)) (hi := (280660287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14023887350481 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14023887350481 / 8000000000000) = 1/(250000000000 / 14023887350481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4027056473 / 1000000000) (4027056479 / 1000000000) (Real.log (14023887350481 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14023887350481 / 250000000000) = -Real.log (250000000000 / 14023887350481) := by
    rw [show ((14023887350481 / 250000000000) : ℝ) = ((250000000000 / 14023887350481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1008908637 / 250000000) ≤ -Real.log (500000000000 / 28289405498777) ∧
    -Real.log (500000000000 / 28289405498777) ≤ (2017817277 / 500000000) := by
  have h := checkLog_sound (w := (12289405498777 / 44289405498777)) (n := 12)
    (lo := (71237331 / 125000000)) (hi := (569898649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28289405498777 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28289405498777 / 16000000000000) = 1/(500000000000 / 28289405498777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1008908637 / 250000000) (2017817277 / 500000000) (Real.log (28289405498777 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28289405498777 / 500000000000) = -Real.log (500000000000 / 28289405498777) := by
    rw [show ((28289405498777 / 500000000000) : ℝ) = ((500000000000 / 28289405498777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0097

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0098Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0098
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

theorem reflection_log_1_neg : (671787873 / 1000000000) ≤ -Real.log (12800 / 25059) ∧
    -Real.log (12800 / 25059) ≤ (335893937 / 500000000) := by
  have h := checkLog_sound (w := (12259 / 37859)) (n := 12)
    (lo := (671787873 / 1000000000)) (hi := (335893937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25059 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25059 / 12800) = 1/(12800 / 25059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (671787873 / 1000000000) (335893937 / 500000000) (Real.log (25059 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25059 / 12800) = -Real.log (12800 / 25059) := by
    rw [show ((25059 / 12800) : ℝ) = ((12800 / 25059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197736323 / 62500000) ≤ -Real.log (541 / 12800) ∧
    -Real.log (541 / 12800) ≤ (3163781173 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 541) = 1/(541 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3163781173 / 1000000000) (-197736323 / 62500000) (Real.log (541 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335799151 / 500000000) ≤ -Real.log (51200 / 100217) ∧
    -Real.log (51200 / 100217) ≤ (671598303 / 1000000000) := by
  have h := checkLog_sound (w := (49017 / 151417)) (n := 12)
    (lo := (335799151 / 500000000)) (hi := (671598303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100217 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100217 / 51200) = 1/(51200 / 100217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335799151 / 500000000) (671598303 / 1000000000) (Real.log (100217 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100217 / 51200) = -Real.log (51200 / 100217) := by
    rw [show ((100217 / 51200) : ℝ) = ((51200 / 100217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (788759863 / 250000000) ≤ -Real.log (2183 / 51200) ∧
    -Real.log (2183 / 51200) ≤ (3155039457 / 1000000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2183) = 1/(2183 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3155039457 / 1000000000) (-788759863 / 250000000) (Real.log (2183 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (64996237 / 100000000) ≤ -Real.log (6400 / 12259) ∧
    -Real.log (6400 / 12259) ≤ (649962371 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 18659)) (n := 12)
    (lo := (64996237 / 100000000)) (hi := (649962371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12259 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12259 / 6400) = 1/(6400 / 12259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (64996237 / 100000000) (649962371 / 1000000000) (Real.log (12259 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12259 / 6400) = -Real.log (6400 / 12259) := by
    rw [show ((12259 / 6400) : ℝ) = ((6400 / 12259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617658497 / 250000000) ≤ -Real.log (541 / 6400) ∧
    -Real.log (541 / 6400) ≤ (308829249 / 125000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 541) = 1/(541 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-308829249 / 125000000) (-617658497 / 250000000) (Real.log (541 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25982993 / 40000000) ≤ -Real.log (25600 / 49017) ∧
    -Real.log (25600 / 49017) ≤ (324787413 / 500000000) := by
  have h := checkLog_sound (w := (23417 / 74617)) (n := 12)
    (lo := (25982993 / 40000000)) (hi := (324787413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49017 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49017 / 25600) = 1/(25600 / 49017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25982993 / 40000000) (324787413 / 500000000) (Real.log (49017 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49017 / 25600) = -Real.log (25600 / 49017) := by
    rw [show ((49017 / 25600) : ℝ) = ((25600 / 49017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153868267 / 62500000) ≤ -Real.log (2183 / 25600) ∧
    -Real.log (2183 / 25600) ≤ (615473069 / 250000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2183) = 1/(2183 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-615473069 / 250000000) (-153868267 / 62500000) (Real.log (2183 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42218647 / 62500000) ≤ -Real.log (250000 / 491253) ∧
    -Real.log (250000 / 491253) ≤ (675498353 / 1000000000) := by
  have h := checkLog_sound (w := (241253 / 741253)) (n := 12)
    (lo := (42218647 / 62500000)) (hi := (675498353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491253 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491253 / 250000) = 1/(250000 / 491253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42218647 / 62500000) (675498353 / 1000000000) (Real.log (491253 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (491253 / 250000) = -Real.log (250000 / 491253) := by
    rw [show ((491253 / 250000) : ℝ) = ((250000 / 491253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3352750131 / 1000000000) ≤ -Real.log (8747 / 250000) ∧
    -Real.log (8747 / 250000) ≤ (419093767 / 125000000) := by
  have h := checkLog_sound (w := (3439 / 12186)) (n := 12)
    (lo := (580161411 / 1000000000)) (hi := (145040353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8747) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8747) = 1/(8747 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-419093767 / 125000000) (-3352750131 / 1000000000) (Real.log (8747 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135128981 / 200000000) ≤ -Real.log (10000 / 19653) ∧
    -Real.log (10000 / 19653) ≤ (337822453 / 500000000) := by
  have h := checkLog_sound (w := (9653 / 29653)) (n := 12)
    (lo := (135128981 / 200000000)) (hi := (337822453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19653 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19653 / 10000) = 1/(10000 / 19653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135128981 / 200000000) (337822453 / 500000000) (Real.log (19653 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19653 / 10000) = -Real.log (10000 / 19653) := by
    rw [show ((19653 / 10000) : ℝ) = ((10000 / 19653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3361015589 / 1000000000) ≤ -Real.log (347 / 10000) ∧
    -Real.log (347 / 10000) ≤ (1680507797 / 500000000) := by
  have h := checkLog_sound (w := (139 / 486)) (n := 12)
    (lo := (588426869 / 1000000000)) (hi := (58842687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 347) = 1/(347 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1680507797 / 500000000) (-3361015589 / 1000000000) (Real.log (347 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135065571 / 200000000) ≤ -Real.log (1000000 / 1964677) ∧
    -Real.log (1000000 / 1964677) ≤ (42207991 / 62500000) := by
  have h := checkLog_sound (w := (964677 / 2964677)) (n := 12)
    (lo := (135065571 / 200000000)) (hi := (42207991 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964677 / 1000000) = 1/(1000000 / 1964677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135065571 / 200000000) (42207991 / 62500000) (Real.log (1964677 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964677 / 1000000) = -Real.log (1000000 / 1964677) := by
    rw [show ((1964677 / 1000000) : ℝ) = ((1000000 / 1964677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1671610483 / 500000000) ≤ -Real.log (35323 / 1000000) ∧
    -Real.log (35323 / 1000000) ≤ (3343220971 / 1000000000) := by
  have h := checkLog_sound (w := (27177 / 97823)) (n := 12)
    (lo := (285316123 / 500000000)) (hi := (570632247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35323) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35323) = 1/(35323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3343220971 / 1000000000) (-1671610483 / 500000000) (Real.log (35323 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135095599 / 200000000) ≤ -Real.log (250000 / 491243) ∧
    -Real.log (250000 / 491243) ≤ (168869499 / 250000000) := by
  have h := checkLog_sound (w := (241243 / 741243)) (n := 12)
    (lo := (135095599 / 200000000)) (hi := (168869499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491243 / 250000) = 1/(250000 / 491243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135095599 / 200000000) (168869499 / 250000000) (Real.log (491243 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (491243 / 250000) = -Real.log (250000 / 491243) := by
    rw [show ((491243 / 250000) : ℝ) = ((250000 / 491243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (670321507 / 200000000) ≤ -Real.log (8757 / 250000) ∧
    -Real.log (8757 / 250000) ≤ (167580377 / 50000000) := by
  have h := checkLog_sound (w := (3434 / 12191)) (n := 12)
    (lo := (115803763 / 200000000)) (hi := (9047169 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8757) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8757) = 1/(8757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-167580377 / 50000000) (-670321507 / 200000000) (Real.log (8757 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2014124241 / 500000000) ≤ -Real.log (125000000000 / 7020306962387) ∧
    -Real.log (125000000000 / 7020306962387) ≤ (503531061 / 125000000) := by
  have h := checkLog_sound (w := (3020306962387 / 11020306962387)) (n := 12)
    (lo := (281256291 / 500000000)) (hi := (562512583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7020306962387 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7020306962387 / 4000000000000) = 1/(125000000000 / 7020306962387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2014124241 / 500000000) (503531061 / 125000000) (Real.log (7020306962387 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7020306962387 / 125000000000) = -Real.log (125000000000 / 7020306962387) := by
    rw [show ((7020306962387 / 125000000000) : ℝ) = ((125000000000 / 7020306962387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2018330247 / 500000000) ≤ -Real.log (100000000000 / 5663688760807) ∧
    -Real.log (100000000000 / 5663688760807) ≤ (8073321 / 2000000) := by
  have h := checkLog_sound (w := (2463688760807 / 8863688760807)) (n := 12)
    (lo := (285462297 / 500000000)) (hi := (114184919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5663688760807 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5663688760807 / 3200000000000) = 1/(100000000000 / 5663688760807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2018330247 / 500000000) (8073321 / 2000000) (Real.log (5663688760807 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5663688760807 / 100000000000) = -Real.log (100000000000 / 5663688760807) := by
    rw [show ((5663688760807 / 100000000000) : ℝ) = ((100000000000 / 5663688760807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4018548821 / 1000000000) ≤ -Real.log (20000000000 / 1112406647227) ∧
    -Real.log (20000000000 / 1112406647227) ≤ (4018548827 / 1000000000) := by
  have h := checkLog_sound (w := (472406647227 / 1752406647227)) (n := 12)
    (lo := (552812921 / 1000000000)) (hi := (276406461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112406647227 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1112406647227 / 640000000000) = 1/(20000000000 / 1112406647227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4018548821 / 1000000000) (4018548827 / 1000000000) (Real.log (1112406647227 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1112406647227 / 20000000000) = -Real.log (20000000000 / 1112406647227) := by
    rw [show ((1112406647227 / 20000000000) : ℝ) = ((20000000000 / 1112406647227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (402708553 / 100000000) ≤ -Real.log (500000000000 / 28048589699669) ∧
    -Real.log (500000000000 / 28048589699669) ≤ (125846423 / 31250000) := by
  have h := checkLog_sound (w := (12048589699669 / 44048589699669)) (n := 12)
    (lo := (56134963 / 100000000)) (hi := (561349631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28048589699669 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28048589699669 / 16000000000000) = 1/(500000000000 / 28048589699669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (402708553 / 100000000) (125846423 / 31250000) (Real.log (28048589699669 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28048589699669 / 500000000000) = -Real.log (500000000000 / 28048589699669) := by
    rw [show ((28048589699669 / 500000000000) : ℝ) = ((500000000000 / 28048589699669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0098

end


