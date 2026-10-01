-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0267Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0267Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:28:43.796123+00:00
-- url     : https://prove2.me/theorems/b5dba0b3-9d8e-4fcb-8b59-323feeca0cbd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0267Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0268Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0267Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0268Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0269Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0270Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0271Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0272Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0273Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0267Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0268Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0269Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0270Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0271Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0272Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0273Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0267Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0268Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0269Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0270Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0271Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0272Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0273Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0267Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0268Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0269Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0270Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0271Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0272Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0273Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0267Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0267
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

theorem reflection_log_1_neg : (235103001 / 1000000000) ≤ -Real.log (5120 / 6477) ∧
    -Real.log (5120 / 6477) ≤ (117551501 / 500000000) := by
  have h := checkLog_sound (w := (1357 / 11597)) (n := 12)
    (lo := (235103001 / 1000000000)) (hi := (117551501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6477 / 5120) = 1/(5120 / 6477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235103001 / 1000000000) (117551501 / 500000000) (Real.log (6477 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6477 / 5120) = -Real.log (5120 / 6477) := by
    rw [show ((6477 / 5120) : ℝ) = ((5120 / 6477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307937927 / 1000000000) ≤ -Real.log (3763 / 5120) ∧
    -Real.log (3763 / 5120) ≤ (38492241 / 125000000) := by
  have h := checkLog_sound (w := (1357 / 8883)) (n := 12)
    (lo := (307937927 / 1000000000)) (hi := (38492241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3763) = 1/(3763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-38492241 / 125000000) (-307937927 / 1000000000) (Real.log (3763 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58659929 / 250000000) ≤ -Real.log (2560 / 3237) ∧
    -Real.log (2560 / 3237) ≤ (234639717 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 5797)) (n := 12)
    (lo := (58659929 / 250000000)) (hi := (234639717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3237 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3237 / 2560) = 1/(2560 / 3237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58659929 / 250000000) (234639717 / 1000000000) (Real.log (3237 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3237 / 2560) = -Real.log (2560 / 3237) := by
    rw [show ((3237 / 2560) : ℝ) = ((2560 / 3237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19196313 / 62500000) ≤ -Real.log (1883 / 2560) ∧
    -Real.log (1883 / 2560) ≤ (307141009 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 4443)) (n := 12)
    (lo := (19196313 / 62500000)) (hi := (307141009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1883) = 1/(1883 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-307141009 / 1000000000) (-19196313 / 62500000) (Real.log (1883 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106329699 / 250000000) ≤ -Real.log (2560 / 3917) ∧
    -Real.log (2560 / 3917) ≤ (425318797 / 1000000000) := by
  have h := checkLog_sound (w := (1357 / 6477)) (n := 12)
    (lo := (106329699 / 250000000)) (hi := (425318797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3917 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3917 / 2560) = 1/(2560 / 3917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106329699 / 250000000) (425318797 / 1000000000) (Real.log (3917 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3917 / 2560) = -Real.log (2560 / 3917) := by
    rw [show ((3917 / 2560) : ℝ) = ((2560 / 3917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (37759441 / 50000000) ≤ -Real.log (1203 / 2560) ∧
    -Real.log (1203 / 2560) ≤ (377594411 / 500000000) := by
  have h := checkLog_sound (w := (77 / 2483)) (n := 12)
    (lo := (1551041 / 25000000)) (hi := (62041641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1203) = 1/(1203 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-377594411 / 500000000) (-37759441 / 50000000) (Real.log (1203 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42455261 / 100000000) ≤ -Real.log (1280 / 1957) ∧
    -Real.log (1280 / 1957) ≤ (424552611 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 3237)) (n := 12)
    (lo := (42455261 / 100000000)) (hi := (424552611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1280) = 1/(1280 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42455261 / 100000000) (424552611 / 1000000000) (Real.log (1957 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1957 / 1280) = -Real.log (1280 / 1957) := by
    rw [show ((1957 / 1280) : ℝ) = ((1280 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (752698159 / 1000000000) ≤ -Real.log (603 / 1280) ∧
    -Real.log (603 / 1280) ≤ (752698161 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 1243)) (n := 12)
    (lo := (59550979 / 1000000000)) (hi := (2977549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 603) = 1/(603 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-752698161 / 1000000000) (-752698159 / 1000000000) (Real.log (603 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (321322339 / 1000000000) ≤ -Real.log (20000 / 27579) ∧
    -Real.log (20000 / 27579) ≤ (16066117 / 50000000) := by
  have h := checkLog_sound (w := (7579 / 47579)) (n := 12)
    (lo := (321322339 / 1000000000)) (hi := (16066117 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27579 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27579 / 20000) = 1/(20000 / 27579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (321322339 / 1000000000) (16066117 / 50000000) (Real.log (27579 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27579 / 20000) = -Real.log (20000 / 27579) := by
    rw [show ((27579 / 20000) : ℝ) = ((20000 / 27579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (119085921 / 250000000) ≤ -Real.log (12421 / 20000) ∧
    -Real.log (12421 / 20000) ≤ (95268737 / 200000000) := by
  have h := checkLog_sound (w := (7579 / 32421)) (n := 12)
    (lo := (119085921 / 250000000)) (hi := (95268737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12421) = 1/(12421 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95268737 / 200000000) (-119085921 / 250000000) (Real.log (12421 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (80487539 / 250000000) ≤ -Real.log (125000 / 172477) ∧
    -Real.log (125000 / 172477) ≤ (321950157 / 1000000000) := by
  have h := checkLog_sound (w := (47477 / 297477)) (n := 12)
    (lo := (80487539 / 250000000)) (hi := (321950157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172477 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172477 / 125000) = 1/(125000 / 172477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (80487539 / 250000000) (321950157 / 1000000000) (Real.log (172477 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (172477 / 125000) = -Real.log (125000 / 172477) := by
    rw [show ((172477 / 125000) : ℝ) = ((125000 / 172477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (47773907 / 100000000) ≤ -Real.log (77523 / 125000) ∧
    -Real.log (77523 / 125000) ≤ (477739071 / 1000000000) := by
  have h := checkLog_sound (w := (47477 / 202523)) (n := 12)
    (lo := (47773907 / 100000000)) (hi := (477739071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 77523) = 1/(77523 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-477739071 / 1000000000) (-47773907 / 100000000) (Real.log (77523 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (61527449 / 250000000) ≤ -Real.log (3125 / 3997) ∧
    -Real.log (3125 / 3997) ≤ (246109797 / 1000000000) := by
  have h := checkLog_sound (w := (436 / 3561)) (n := 12)
    (lo := (61527449 / 250000000)) (hi := (246109797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3997 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3997 / 3125) = 1/(3125 / 3997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (61527449 / 250000000) (246109797 / 1000000000) (Real.log (3997 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3997 / 3125) = -Real.log (3125 / 3997) := by
    rw [show ((3997 / 3125) : ℝ) = ((3125 / 3997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (327171621 / 1000000000) ≤ -Real.log (2253 / 3125) ∧
    -Real.log (2253 / 3125) ≤ (163585811 / 500000000) := by
  have h := checkLog_sound (w := (436 / 2689)) (n := 12)
    (lo := (327171621 / 1000000000)) (hi := (163585811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2253) = 1/(2253 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-163585811 / 500000000) (-327171621 / 1000000000) (Real.log (2253 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (246649899 / 1000000000) ≤ -Real.log (1000000 / 1279731) ∧
    -Real.log (1000000 / 1279731) ≤ (2466499 / 10000000) := by
  have h := checkLog_sound (w := (279731 / 2279731)) (n := 12)
    (lo := (246649899 / 1000000000)) (hi := (2466499 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279731 / 1000000) = 1/(1000000 / 1279731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (246649899 / 1000000000) (2466499 / 10000000) (Real.log (1279731 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1279731 / 1000000) = -Real.log (1000000 / 1279731) := by
    rw [show ((1279731 / 1000000) : ℝ) = ((1000000 / 1279731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (13125221 / 40000000) ≤ -Real.log (720269 / 1000000) ∧
    -Real.log (720269 / 1000000) ≤ (164065263 / 500000000) := by
  have h := checkLog_sound (w := (279731 / 1720269)) (n := 12)
    (lo := (13125221 / 40000000)) (hi := (164065263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720269) = 1/(720269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-164065263 / 500000000) (-13125221 / 40000000) (Real.log (720269 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (99708253 / 125000000) ≤ -Real.log (250000000000 / 555088157153) ∧
    -Real.log (250000000000 / 555088157153) ≤ (398833013 / 500000000) := by
  have h := checkLog_sound (w := (55088157153 / 1055088157153)) (n := 12)
    (lo := (26129711 / 250000000)) (hi := (20903769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555088157153 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555088157153 / 500000000000) = 1/(250000000000 / 555088157153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (99708253 / 125000000) (398833013 / 500000000) (Real.log (555088157153 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (555088157153 / 250000000000) = -Real.log (250000000000 / 555088157153) := by
    rw [show ((555088157153 / 250000000000) : ℝ) = ((250000000000 / 555088157153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (799689227 / 1000000000) ≤ -Real.log (500000000000 / 1112424699767) ∧
    -Real.log (500000000000 / 1112424699767) ≤ (799689229 / 1000000000) := by
  have h := checkLog_sound (w := (112424699767 / 2112424699767)) (n := 12)
    (lo := (106542047 / 1000000000)) (hi := (3329439 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112424699767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112424699767 / 1000000000000) = 1/(500000000000 / 1112424699767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (799689227 / 1000000000) (799689229 / 1000000000) (Real.log (1112424699767 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1112424699767 / 500000000000) = -Real.log (500000000000 / 1112424699767) := by
    rw [show ((1112424699767 / 500000000000) : ℝ) = ((500000000000 / 1112424699767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (286640709 / 500000000) ≤ -Real.log (100000000000 / 177407900577) ∧
    -Real.log (100000000000 / 177407900577) ≤ (573281419 / 1000000000) := by
  have h := checkLog_sound (w := (77407900577 / 277407900577)) (n := 12)
    (lo := (286640709 / 500000000)) (hi := (573281419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177407900577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177407900577 / 100000000000) = 1/(100000000000 / 177407900577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (286640709 / 500000000) (573281419 / 1000000000) (Real.log (177407900577 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (177407900577 / 100000000000) = -Real.log (100000000000 / 177407900577) := by
    rw [show ((177407900577 / 100000000000) : ℝ) = ((100000000000 / 177407900577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (22991217 / 40000000) ≤ -Real.log (125000000000 / 222092544591) ∧
    -Real.log (125000000000 / 222092544591) ≤ (287390213 / 500000000) := by
  have h := checkLog_sound (w := (97092544591 / 347092544591)) (n := 12)
    (lo := (22991217 / 40000000)) (hi := (287390213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222092544591 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222092544591 / 125000000000) = 1/(125000000000 / 222092544591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (22991217 / 40000000) (287390213 / 500000000) (Real.log (222092544591 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (222092544591 / 125000000000) = -Real.log (125000000000 / 222092544591) := by
    rw [show ((222092544591 / 125000000000) : ℝ) = ((125000000000 / 222092544591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0267

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0268Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0268
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

theorem reflection_log_1_neg : (58659929 / 250000000) ≤ -Real.log (2560 / 3237) ∧
    -Real.log (2560 / 3237) ≤ (234639717 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 5797)) (n := 12)
    (lo := (58659929 / 250000000)) (hi := (234639717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3237 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3237 / 2560) = 1/(2560 / 3237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58659929 / 250000000) (234639717 / 1000000000) (Real.log (3237 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3237 / 2560) = -Real.log (2560 / 3237) := by
    rw [show ((3237 / 2560) : ℝ) = ((2560 / 3237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19196313 / 62500000) ≤ -Real.log (1883 / 2560) ∧
    -Real.log (1883 / 2560) ≤ (307141009 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 4443)) (n := 12)
    (lo := (19196313 / 62500000)) (hi := (307141009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1883) = 1/(1883 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-307141009 / 1000000000) (-19196313 / 62500000) (Real.log (1883 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (234176217 / 1000000000) ≤ -Real.log (5120 / 6471) ∧
    -Real.log (5120 / 6471) ≤ (117088109 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 11591)) (n := 12)
    (lo := (234176217 / 1000000000)) (hi := (117088109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6471 / 5120) = 1/(5120 / 6471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (234176217 / 1000000000) (117088109 / 500000000) (Real.log (6471 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6471 / 5120) = -Real.log (5120 / 6471) := by
    rw [show ((6471 / 5120) : ℝ) = ((5120 / 6471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (76586181 / 250000000) ≤ -Real.log (3769 / 5120) ∧
    -Real.log (3769 / 5120) ≤ (12253789 / 40000000) := by
  have h := checkLog_sound (w := (1351 / 8889)) (n := 12)
    (lo := (76586181 / 250000000)) (hi := (12253789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3769) = 1/(3769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12253789 / 40000000) (-76586181 / 250000000) (Real.log (3769 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42455261 / 100000000) ≤ -Real.log (1280 / 1957) ∧
    -Real.log (1280 / 1957) ≤ (424552611 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 3237)) (n := 12)
    (lo := (42455261 / 100000000)) (hi := (424552611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1280) = 1/(1280 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42455261 / 100000000) (424552611 / 1000000000) (Real.log (1957 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1957 / 1280) = -Real.log (1280 / 1957) := by
    rw [show ((1957 / 1280) : ℝ) = ((1280 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (752698159 / 1000000000) ≤ -Real.log (603 / 1280) ∧
    -Real.log (603 / 1280) ≤ (752698161 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 1243)) (n := 12)
    (lo := (59550979 / 1000000000)) (hi := (2977549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 603) = 1/(603 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-752698161 / 1000000000) (-752698159 / 1000000000) (Real.log (603 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (423785837 / 1000000000) ≤ -Real.log (2560 / 3911) ∧
    -Real.log (2560 / 3911) ≤ (211892919 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 6471)) (n := 12)
    (lo := (423785837 / 1000000000)) (hi := (211892919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 2560) = 1/(2560 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (423785837 / 1000000000) (211892919 / 500000000) (Real.log (3911 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3911 / 2560) = -Real.log (2560 / 3911) := by
    rw [show ((3911 / 2560) : ℝ) = ((2560 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (375106843 / 500000000) ≤ -Real.log (1209 / 2560) ∧
    -Real.log (1209 / 2560) ≤ (93776711 / 125000000) := by
  have h := checkLog_sound (w := (71 / 2489)) (n := 12)
    (lo := (28533253 / 500000000)) (hi := (57066507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1209) = 1/(1209 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-93776711 / 125000000) (-375106843 / 500000000) (Real.log (1209 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (320695579 / 1000000000) ≤ -Real.log (500000 / 689043) ∧
    -Real.log (500000 / 689043) ≤ (16034779 / 50000000) := by
  have h := checkLog_sound (w := (189043 / 1189043)) (n := 12)
    (lo := (320695579 / 1000000000)) (hi := (16034779 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689043 / 500000) = 1/(500000 / 689043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (320695579 / 1000000000) (16034779 / 50000000) (Real.log (689043 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (689043 / 500000) = -Real.log (500000 / 689043) := by
    rw [show ((689043 / 500000) : ℝ) = ((500000 / 689043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (474953459 / 1000000000) ≤ -Real.log (310957 / 500000) ∧
    -Real.log (310957 / 500000) ≤ (23747673 / 50000000) := by
  have h := checkLog_sound (w := (189043 / 810957)) (n := 12)
    (lo := (474953459 / 1000000000)) (hi := (23747673 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 310957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 310957) = 1/(310957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23747673 / 50000000) (-474953459 / 1000000000) (Real.log (310957 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64264613 / 200000000) ≤ -Real.log (1000000 / 1378951) ∧
    -Real.log (1000000 / 1378951) ≤ (160661533 / 500000000) := by
  have h := checkLog_sound (w := (378951 / 2378951)) (n := 12)
    (lo := (64264613 / 200000000)) (hi := (160661533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378951 / 1000000) = 1/(1000000 / 1378951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64264613 / 200000000) (160661533 / 500000000) (Real.log (1378951 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1378951 / 1000000) = -Real.log (1000000 / 1378951) := by
    rw [show ((1378951 / 1000000) : ℝ) = ((1000000 / 1378951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95269059 / 200000000) ≤ -Real.log (621049 / 1000000) ∧
    -Real.log (621049 / 1000000) ≤ (29771581 / 62500000) := by
  have h := checkLog_sound (w := (378951 / 1621049)) (n := 12)
    (lo := (95269059 / 200000000)) (hi := (29771581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621049) = 1/(621049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29771581 / 62500000) (-95269059 / 200000000) (Real.log (621049 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (122785483 / 500000000) ≤ -Real.log (1000000 / 1278351) ∧
    -Real.log (1000000 / 1278351) ≤ (245570967 / 1000000000) := by
  have h := checkLog_sound (w := (278351 / 2278351)) (n := 12)
    (lo := (122785483 / 500000000)) (hi := (245570967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278351 / 1000000) = 1/(1000000 / 1278351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (122785483 / 500000000) (245570967 / 1000000000) (Real.log (1278351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1278351 / 1000000) = -Real.log (1000000 / 1278351) := by
    rw [show ((1278351 / 1000000) : ℝ) = ((1000000 / 1278351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (326216407 / 1000000000) ≤ -Real.log (721649 / 1000000) ∧
    -Real.log (721649 / 1000000) ≤ (40777051 / 125000000) := by
  have h := checkLog_sound (w := (278351 / 1721649)) (n := 12)
    (lo := (326216407 / 1000000000)) (hi := (40777051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721649) = 1/(721649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40777051 / 125000000) (-326216407 / 1000000000) (Real.log (721649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (123055289 / 500000000) ≤ -Real.log (1000000 / 1279041) ∧
    -Real.log (1000000 / 1279041) ≤ (246110579 / 1000000000) := by
  have h := checkLog_sound (w := (279041 / 2279041)) (n := 12)
    (lo := (123055289 / 500000000)) (hi := (246110579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279041 / 1000000) = 1/(1000000 / 1279041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (123055289 / 500000000) (246110579 / 1000000000) (Real.log (1279041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1279041 / 1000000) = -Real.log (1000000 / 1279041) := by
    rw [show ((1279041 / 1000000) : ℝ) = ((1000000 / 1279041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20448313 / 62500000) ≤ -Real.log (720959 / 1000000) ∧
    -Real.log (720959 / 1000000) ≤ (327173009 / 1000000000) := by
  have h := checkLog_sound (w := (279041 / 1720959)) (n := 12)
    (lo := (20448313 / 62500000)) (hi := (327173009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720959) = 1/(720959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-327173009 / 1000000000) (-20448313 / 62500000) (Real.log (720959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (397824519 / 500000000) ≤ -Real.log (50000000000 / 110793936139) ∧
    -Real.log (50000000000 / 110793936139) ≤ (9945613 / 12500000) := by
  have h := checkLog_sound (w := (10793936139 / 210793936139)) (n := 12)
    (lo := (51250929 / 500000000)) (hi := (102501859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110793936139 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110793936139 / 100000000000) = 1/(50000000000 / 110793936139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (397824519 / 500000000) (9945613 / 12500000) (Real.log (110793936139 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (110793936139 / 50000000000) = -Real.log (50000000000 / 110793936139) := by
    rw [show ((110793936139 / 50000000000) : ℝ) = ((50000000000 / 110793936139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (797668359 / 1000000000) ≤ -Real.log (500000000000 / 1110178906979) ∧
    -Real.log (500000000000 / 1110178906979) ≤ (797668361 / 1000000000) := by
  have h := checkLog_sound (w := (110178906979 / 2110178906979)) (n := 12)
    (lo := (104521179 / 1000000000)) (hi := (5226059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110178906979 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110178906979 / 1000000000000) = 1/(500000000000 / 1110178906979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (797668359 / 1000000000) (797668361 / 1000000000) (Real.log (1110178906979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1110178906979 / 500000000000) = -Real.log (500000000000 / 1110178906979) := by
    rw [show ((1110178906979 / 500000000000) : ℝ) = ((500000000000 / 1110178906979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (285893687 / 500000000) ≤ -Real.log (500000000000 / 885715216123) ∧
    -Real.log (500000000000 / 885715216123) ≤ (4574299 / 8000000) := by
  have h := checkLog_sound (w := (385715216123 / 1385715216123)) (n := 12)
    (lo := (285893687 / 500000000)) (hi := (4574299 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885715216123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885715216123 / 500000000000) = 1/(500000000000 / 885715216123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (285893687 / 500000000) (4574299 / 8000000) (Real.log (885715216123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (885715216123 / 500000000000) = -Real.log (500000000000 / 885715216123) := by
    rw [show ((885715216123 / 500000000000) : ℝ) = ((500000000000 / 885715216123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (573283587 / 1000000000) ≤ -Real.log (500000000000 / 887041426767) ∧
    -Real.log (500000000000 / 887041426767) ≤ (143320897 / 250000000) := by
  have h := checkLog_sound (w := (387041426767 / 1387041426767)) (n := 12)
    (lo := (573283587 / 1000000000)) (hi := (143320897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887041426767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887041426767 / 500000000000) = 1/(500000000000 / 887041426767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (573283587 / 1000000000) (143320897 / 250000000) (Real.log (887041426767 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (887041426767 / 500000000000) = -Real.log (500000000000 / 887041426767) := by
    rw [show ((887041426767 / 500000000000) : ℝ) = ((500000000000 / 887041426767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0268

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0269Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0269
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

theorem reflection_log_1_neg : (234176217 / 1000000000) ≤ -Real.log (5120 / 6471) ∧
    -Real.log (5120 / 6471) ≤ (117088109 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 11591)) (n := 12)
    (lo := (234176217 / 1000000000)) (hi := (117088109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6471 / 5120) = 1/(5120 / 6471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (234176217 / 1000000000) (117088109 / 500000000) (Real.log (6471 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6471 / 5120) = -Real.log (5120 / 6471) := by
    rw [show ((6471 / 5120) : ℝ) = ((5120 / 6471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (76586181 / 250000000) ≤ -Real.log (3769 / 5120) ∧
    -Real.log (3769 / 5120) ≤ (12253789 / 40000000) := by
  have h := checkLog_sound (w := (1351 / 8889)) (n := 12)
    (lo := (76586181 / 250000000)) (hi := (12253789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3769) = 1/(3769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12253789 / 40000000) (-76586181 / 250000000) (Real.log (3769 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116856251 / 500000000) ≤ -Real.log (1280 / 1617) ∧
    -Real.log (1280 / 1617) ≤ (233712503 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2897)) (n := 12)
    (lo := (116856251 / 500000000)) (hi := (233712503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1280) = 1/(1280 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116856251 / 500000000) (233712503 / 1000000000) (Real.log (1617 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1617 / 1280) = -Real.log (1280 / 1617) := by
    rw [show ((1617 / 1280) : ℝ) = ((1280 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (152774537 / 500000000) ≤ -Real.log (943 / 1280) ∧
    -Real.log (943 / 1280) ≤ (12221963 / 40000000) := by
  have h := checkLog_sound (w := (337 / 2223)) (n := 12)
    (lo := (152774537 / 500000000)) (hi := (12221963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 943) = 1/(943 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12221963 / 40000000) (-152774537 / 500000000) (Real.log (943 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (423785837 / 1000000000) ≤ -Real.log (2560 / 3911) ∧
    -Real.log (2560 / 3911) ≤ (211892919 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 6471)) (n := 12)
    (lo := (423785837 / 1000000000)) (hi := (211892919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 2560) = 1/(2560 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (423785837 / 1000000000) (211892919 / 500000000) (Real.log (3911 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3911 / 2560) = -Real.log (2560 / 3911) := by
    rw [show ((3911 / 2560) : ℝ) = ((2560 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (375106843 / 500000000) ≤ -Real.log (1209 / 2560) ∧
    -Real.log (1209 / 2560) ≤ (93776711 / 125000000) := by
  have h := checkLog_sound (w := (71 / 2489)) (n := 12)
    (lo := (28533253 / 500000000)) (hi := (57066507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1209) = 1/(1209 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-93776711 / 125000000) (-375106843 / 500000000) (Real.log (1209 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16920739 / 40000000) ≤ -Real.log (640 / 977) ∧
    -Real.log (640 / 977) ≤ (105754619 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1617)) (n := 12)
    (lo := (16920739 / 40000000)) (hi := (105754619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 640) = 1/(640 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16920739 / 40000000) (105754619 / 250000000) (Real.log (977 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (977 / 640) = -Real.log (640 / 977) := by
    rw [show ((977 / 640) : ℝ) = ((640 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (74773537 / 100000000) ≤ -Real.log (303 / 640) ∧
    -Real.log (303 / 640) ≤ (186933843 / 250000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 303) = 1/(303 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-186933843 / 250000000) (-74773537 / 100000000) (Real.log (303 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3200677 / 10000000) ≤ -Real.log (1000000 / 1377221) ∧
    -Real.log (1000000 / 1377221) ≤ (320067701 / 1000000000) := by
  have h := checkLog_sound (w := (377221 / 2377221)) (n := 12)
    (lo := (3200677 / 10000000)) (hi := (320067701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377221 / 1000000) = 1/(1000000 / 1377221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3200677 / 10000000) (320067701 / 1000000000) (Real.log (1377221 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1377221 / 1000000) = -Real.log (1000000 / 1377221) := by
    rw [show ((1377221 / 1000000) : ℝ) = ((1000000 / 1377221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236781779 / 500000000) ≤ -Real.log (622779 / 1000000) ∧
    -Real.log (622779 / 1000000) ≤ (473563559 / 1000000000) := by
  have h := checkLog_sound (w := (377221 / 1622779)) (n := 12)
    (lo := (236781779 / 500000000)) (hi := (473563559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 622779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 622779) = 1/(622779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-473563559 / 1000000000) (-236781779 / 500000000) (Real.log (622779 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64139261 / 200000000) ≤ -Real.log (1000000 / 1378087) ∧
    -Real.log (1000000 / 1378087) ≤ (160348153 / 500000000) := by
  have h := checkLog_sound (w := (378087 / 2378087)) (n := 12)
    (lo := (64139261 / 200000000)) (hi := (160348153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378087 / 1000000) = 1/(1000000 / 1378087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64139261 / 200000000) (160348153 / 500000000) (Real.log (1378087 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1378087 / 1000000) = -Real.log (1000000 / 1378087) := by
    rw [show ((1378087 / 1000000) : ℝ) = ((1000000 / 1378087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (474955067 / 1000000000) ≤ -Real.log (621913 / 1000000) ∧
    -Real.log (621913 / 1000000) ≤ (118738767 / 250000000) := by
  have h := checkLog_sound (w := (378087 / 1621913)) (n := 12)
    (lo := (474955067 / 1000000000)) (hi := (118738767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621913) = 1/(621913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118738767 / 250000000) (-474955067 / 1000000000) (Real.log (621913 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (245032627 / 1000000000) ≤ -Real.log (1000000 / 1277663) ∧
    -Real.log (1000000 / 1277663) ≤ (61258157 / 250000000) := by
  have h := checkLog_sound (w := (277663 / 2277663)) (n := 12)
    (lo := (245032627 / 1000000000)) (hi := (61258157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277663 / 1000000) = 1/(1000000 / 1277663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (245032627 / 1000000000) (61258157 / 250000000) (Real.log (1277663 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1277663 / 1000000) = -Real.log (1000000 / 1277663) := by
    rw [show ((1277663 / 1000000) : ℝ) = ((1000000 / 1277663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (325263489 / 1000000000) ≤ -Real.log (722337 / 1000000) ∧
    -Real.log (722337 / 1000000) ≤ (32526349 / 100000000) := by
  have h := checkLog_sound (w := (277663 / 1722337)) (n := 12)
    (lo := (325263489 / 1000000000)) (hi := (32526349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 722337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 722337) = 1/(722337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-32526349 / 100000000) (-325263489 / 1000000000) (Real.log (722337 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61392937 / 250000000) ≤ -Real.log (62500 / 79897) ∧
    -Real.log (62500 / 79897) ≤ (245571749 / 1000000000) := by
  have h := checkLog_sound (w := (17397 / 142397)) (n := 12)
    (lo := (61392937 / 250000000)) (hi := (245571749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79897 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79897 / 62500) = 1/(62500 / 79897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61392937 / 250000000) (245571749 / 1000000000) (Real.log (79897 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79897 / 62500) = -Real.log (62500 / 79897) := by
    rw [show ((79897 / 62500) : ℝ) = ((62500 / 79897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (326217793 / 1000000000) ≤ -Real.log (45103 / 62500) ∧
    -Real.log (45103 / 62500) ≤ (163108897 / 500000000) := by
  have h := checkLog_sound (w := (17397 / 107603)) (n := 12)
    (lo := (326217793 / 1000000000)) (hi := (163108897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45103) = 1/(45103 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-163108897 / 500000000) (-326217793 / 1000000000) (Real.log (45103 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (396815629 / 500000000) ≤ -Real.log (125000000000 / 276426509243) ∧
    -Real.log (125000000000 / 276426509243) ≤ (39681563 / 50000000) := by
  have h := checkLog_sound (w := (26426509243 / 526426509243)) (n := 12)
    (lo := (50242039 / 500000000)) (hi := (100484079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276426509243 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(276426509243 / 250000000000) = 1/(125000000000 / 276426509243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (396815629 / 500000000) (39681563 / 50000000) (Real.log (276426509243 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (276426509243 / 125000000000) = -Real.log (125000000000 / 276426509243) := by
    rw [show ((276426509243 / 125000000000) : ℝ) = ((125000000000 / 276426509243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (198912843 / 250000000) ≤ -Real.log (31250000000 / 69246371679) ∧
    -Real.log (31250000000 / 69246371679) ≤ (397825687 / 500000000) := by
  have h := checkLog_sound (w := (6746371679 / 131746371679)) (n := 12)
    (lo := (400407 / 3906250)) (hi := (102504193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69246371679 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69246371679 / 62500000000) = 1/(31250000000 / 69246371679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (198912843 / 250000000) (397825687 / 500000000) (Real.log (69246371679 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (69246371679 / 31250000000) = -Real.log (31250000000 / 69246371679) := by
    rw [show ((69246371679 / 31250000000) : ℝ) = ((31250000000 / 69246371679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (570296117 / 1000000000) ≤ -Real.log (500000000000 / 884395372243) ∧
    -Real.log (500000000000 / 884395372243) ≤ (285148059 / 500000000) := by
  have h := checkLog_sound (w := (384395372243 / 1384395372243)) (n := 12)
    (lo := (570296117 / 1000000000)) (hi := (285148059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884395372243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884395372243 / 500000000000) = 1/(500000000000 / 884395372243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (570296117 / 1000000000) (285148059 / 500000000) (Real.log (884395372243 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (884395372243 / 500000000000) = -Real.log (500000000000 / 884395372243) := by
    rw [show ((884395372243 / 500000000000) : ℝ) = ((500000000000 / 884395372243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (571789541 / 1000000000) ≤ -Real.log (500000000000 / 885717136333) ∧
    -Real.log (500000000000 / 885717136333) ≤ (285894771 / 500000000) := by
  have h := checkLog_sound (w := (385717136333 / 1385717136333)) (n := 12)
    (lo := (571789541 / 1000000000)) (hi := (285894771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885717136333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885717136333 / 500000000000) = 1/(500000000000 / 885717136333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (571789541 / 1000000000) (285894771 / 500000000) (Real.log (885717136333 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (885717136333 / 500000000000) = -Real.log (500000000000 / 885717136333) := by
    rw [show ((885717136333 / 500000000000) : ℝ) = ((500000000000 / 885717136333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0269

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0270Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0270
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

theorem reflection_log_1_neg : (116856251 / 500000000) ≤ -Real.log (1280 / 1617) ∧
    -Real.log (1280 / 1617) ≤ (233712503 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2897)) (n := 12)
    (lo := (116856251 / 500000000)) (hi := (233712503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1280) = 1/(1280 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116856251 / 500000000) (233712503 / 1000000000) (Real.log (1617 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1617 / 1280) = -Real.log (1280 / 1617) := by
    rw [show ((1617 / 1280) : ℝ) = ((1280 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (152774537 / 500000000) ≤ -Real.log (943 / 1280) ∧
    -Real.log (943 / 1280) ≤ (12221963 / 40000000) := by
  have h := checkLog_sound (w := (337 / 2223)) (n := 12)
    (lo := (152774537 / 500000000)) (hi := (12221963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 943) = 1/(943 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12221963 / 40000000) (-152774537 / 500000000) (Real.log (943 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (233248573 / 1000000000) ≤ -Real.log (1024 / 1293) ∧
    -Real.log (1024 / 1293) ≤ (116624287 / 500000000) := by
  have h := checkLog_sound (w := (269 / 2317)) (n := 12)
    (lo := (233248573 / 1000000000)) (hi := (116624287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1024) = 1/(1024 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (233248573 / 1000000000) (116624287 / 500000000) (Real.log (1293 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1293 / 1024) = -Real.log (1024 / 1293) := by
    rw [show ((1293 / 1024) : ℝ) = ((1024 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38094257 / 125000000) ≤ -Real.log (755 / 1024) ∧
    -Real.log (755 / 1024) ≤ (304754057 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1779)) (n := 12)
    (lo := (38094257 / 125000000)) (hi := (304754057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 755) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 755) = 1/(755 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-304754057 / 1000000000) (-38094257 / 125000000) (Real.log (755 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16920739 / 40000000) ≤ -Real.log (640 / 977) ∧
    -Real.log (640 / 977) ≤ (105754619 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1617)) (n := 12)
    (lo := (16920739 / 40000000)) (hi := (105754619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 640) = 1/(640 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16920739 / 40000000) (105754619 / 250000000) (Real.log (977 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (977 / 640) = -Real.log (640 / 977) := by
    rw [show ((977 / 640) : ℝ) = ((640 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74773537 / 100000000) ≤ -Real.log (303 / 640) ∧
    -Real.log (303 / 640) ≤ (186933843 / 250000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 303) = 1/(303 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-186933843 / 250000000) (-74773537 / 100000000) (Real.log (303 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (105562631 / 250000000) ≤ -Real.log (512 / 781) ∧
    -Real.log (512 / 781) ≤ (16890021 / 40000000) := by
  have h := checkLog_sound (w := (269 / 1293)) (n := 12)
    (lo := (105562631 / 250000000)) (hi := (16890021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781 / 512) = 1/(512 / 781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (105562631 / 250000000) (16890021 / 40000000) (Real.log (781 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (781 / 512) = -Real.log (512 / 781) := by
    rw [show ((781 / 512) : ℝ) = ((512 / 781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (745263181 / 1000000000) ≤ -Real.log (243 / 512) ∧
    -Real.log (243 / 512) ≤ (745263183 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 499)) (n := 12)
    (lo := (52116001 / 1000000000)) (hi := (26058001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 243) = 1/(243 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-745263183 / 1000000000) (-745263181 / 1000000000) (Real.log (243 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (319440153 / 1000000000) ≤ -Real.log (1000000 / 1376357) ∧
    -Real.log (1000000 / 1376357) ≤ (159720077 / 500000000) := by
  have h := checkLog_sound (w := (376357 / 2376357)) (n := 12)
    (lo := (319440153 / 1000000000)) (hi := (159720077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1376357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1376357 / 1000000) = 1/(1000000 / 1376357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (319440153 / 1000000000) (159720077 / 500000000) (Real.log (1376357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1376357 / 1000000) = -Real.log (1000000 / 1376357) := by
    rw [show ((1376357 / 1000000) : ℝ) = ((1000000 / 1376357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (472177189 / 1000000000) ≤ -Real.log (623643 / 1000000) ∧
    -Real.log (623643 / 1000000) ≤ (47217719 / 100000000) := by
  have h := checkLog_sound (w := (376357 / 1623643)) (n := 12)
    (lo := (472177189 / 1000000000)) (hi := (47217719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 623643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 623643) = 1/(623643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-47217719 / 100000000) (-472177189 / 1000000000) (Real.log (623643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (160034213 / 500000000) ≤ -Real.log (500000 / 688611) ∧
    -Real.log (500000 / 688611) ≤ (320068427 / 1000000000) := by
  have h := checkLog_sound (w := (188611 / 1188611)) (n := 12)
    (lo := (160034213 / 500000000)) (hi := (320068427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688611 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688611 / 500000) = 1/(500000 / 688611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (160034213 / 500000000) (320068427 / 1000000000) (Real.log (688611 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (688611 / 500000) = -Real.log (500000 / 688611) := by
    rw [show ((688611 / 500000) : ℝ) = ((500000 / 688611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (473565163 / 1000000000) ≤ -Real.log (311389 / 500000) ∧
    -Real.log (311389 / 500000) ≤ (118391291 / 250000000) := by
  have h := checkLog_sound (w := (188611 / 811389)) (n := 12)
    (lo := (473565163 / 1000000000)) (hi := (118391291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311389) = 1/(311389 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118391291 / 250000000) (-473565163 / 1000000000) (Real.log (311389 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (244493999 / 1000000000) ≤ -Real.log (40000 / 51079) ∧
    -Real.log (40000 / 51079) ≤ (122247 / 500000) := by
  have h := checkLog_sound (w := (11079 / 91079)) (n := 12)
    (lo := (244493999 / 1000000000)) (hi := (122247 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51079 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51079 / 40000) = 1/(40000 / 51079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (244493999 / 1000000000) (122247 / 500000) (Real.log (51079 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (51079 / 40000) = -Real.log (40000 / 51079) := by
    rw [show ((51079 / 40000) : ℝ) = ((40000 / 51079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (324311479 / 1000000000) ≤ -Real.log (28921 / 40000) ∧
    -Real.log (28921 / 40000) ≤ (8107787 / 25000000) := by
  have h := checkLog_sound (w := (11079 / 68921)) (n := 12)
    (lo := (324311479 / 1000000000)) (hi := (8107787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28921) = 1/(28921 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8107787 / 25000000) (-324311479 / 1000000000) (Real.log (28921 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24503341 / 100000000) ≤ -Real.log (31250 / 39927) ∧
    -Real.log (31250 / 39927) ≤ (245033411 / 1000000000) := by
  have h := checkLog_sound (w := (8677 / 71177)) (n := 12)
    (lo := (24503341 / 100000000)) (hi := (245033411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39927 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39927 / 31250) = 1/(31250 / 39927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24503341 / 100000000) (245033411 / 1000000000) (Real.log (39927 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39927 / 31250) = -Real.log (31250 / 39927) := by
    rw [show ((39927 / 31250) : ℝ) = ((31250 / 39927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162632437 / 500000000) ≤ -Real.log (22573 / 31250) ∧
    -Real.log (22573 / 31250) ≤ (2602119 / 8000000) := by
  have h := checkLog_sound (w := (8677 / 53823)) (n := 12)
    (lo := (162632437 / 500000000)) (hi := (2602119 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22573) = 1/(22573 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2602119 / 8000000) (-162632437 / 500000000) (Real.log (22573 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (395808671 / 500000000) ≤ -Real.log (500000000000 / 1103481478987) ∧
    -Real.log (500000000000 / 1103481478987) ≤ (12369021 / 15625000) := by
  have h := checkLog_sound (w := (103481478987 / 2103481478987)) (n := 12)
    (lo := (49235081 / 500000000)) (hi := (98470163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103481478987 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1103481478987 / 1000000000000) = 1/(500000000000 / 1103481478987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (395808671 / 500000000) (12369021 / 15625000) (Real.log (1103481478987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1103481478987 / 500000000000) = -Real.log (500000000000 / 1103481478987) := by
    rw [show ((1103481478987 / 500000000000) : ℝ) = ((500000000000 / 1103481478987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79363359 / 100000000) ≤ -Real.log (50000000000 / 110570861527) ∧
    -Real.log (50000000000 / 110570861527) ≤ (99204199 / 125000000) := by
  have h := checkLog_sound (w := (10570861527 / 210570861527)) (n := 12)
    (lo := (10048641 / 100000000)) (hi := (100486411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110570861527 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110570861527 / 100000000000) = 1/(50000000000 / 110570861527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79363359 / 100000000) (99204199 / 125000000) (Real.log (110570861527 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (110570861527 / 50000000000) = -Real.log (50000000000 / 110570861527) := by
    rw [show ((110570861527 / 50000000000) : ℝ) = ((50000000000 / 110570861527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (284402739 / 500000000) ≤ -Real.log (250000000000 / 441539020089) ∧
    -Real.log (250000000000 / 441539020089) ≤ (568805479 / 1000000000) := by
  have h := checkLog_sound (w := (191539020089 / 691539020089)) (n := 12)
    (lo := (284402739 / 500000000)) (hi := (568805479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441539020089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441539020089 / 250000000000) = 1/(250000000000 / 441539020089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (284402739 / 500000000) (568805479 / 1000000000) (Real.log (441539020089 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (441539020089 / 250000000000) = -Real.log (250000000000 / 441539020089) := by
    rw [show ((441539020089 / 250000000000) : ℝ) = ((250000000000 / 441539020089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (142574571 / 250000000) ≤ -Real.log (500000000000 / 884397288797) ∧
    -Real.log (500000000000 / 884397288797) ≤ (114059657 / 200000000) := by
  have h := checkLog_sound (w := (384397288797 / 1384397288797)) (n := 12)
    (lo := (142574571 / 250000000)) (hi := (114059657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884397288797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884397288797 / 500000000000) = 1/(500000000000 / 884397288797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (142574571 / 250000000) (114059657 / 200000000) (Real.log (884397288797 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (884397288797 / 500000000000) = -Real.log (500000000000 / 884397288797) := by
    rw [show ((884397288797 / 500000000000) : ℝ) = ((500000000000 / 884397288797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0270

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0271Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0271
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

theorem reflection_log_1_neg : (233248573 / 1000000000) ≤ -Real.log (1024 / 1293) ∧
    -Real.log (1024 / 1293) ≤ (116624287 / 500000000) := by
  have h := checkLog_sound (w := (269 / 2317)) (n := 12)
    (lo := (233248573 / 1000000000)) (hi := (116624287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1024) = 1/(1024 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (233248573 / 1000000000) (116624287 / 500000000) (Real.log (1293 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1293 / 1024) = -Real.log (1024 / 1293) := by
    rw [show ((1293 / 1024) : ℝ) = ((1024 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38094257 / 125000000) ≤ -Real.log (755 / 1024) ∧
    -Real.log (755 / 1024) ≤ (304754057 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1779)) (n := 12)
    (lo := (38094257 / 125000000)) (hi := (304754057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 755) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 755) = 1/(755 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-304754057 / 1000000000) (-38094257 / 125000000) (Real.log (755 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58196107 / 250000000) ≤ -Real.log (2560 / 3231) ∧
    -Real.log (2560 / 3231) ≤ (232784429 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 5791)) (n := 12)
    (lo := (58196107 / 250000000)) (hi := (232784429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3231 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3231 / 2560) = 1/(2560 / 3231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58196107 / 250000000) (232784429 / 1000000000) (Real.log (3231 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3231 / 2560) = -Real.log (2560 / 3231) := by
    rw [show ((3231 / 2560) : ℝ) = ((2560 / 3231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303959669 / 1000000000) ≤ -Real.log (1889 / 2560) ∧
    -Real.log (1889 / 2560) ≤ (30395967 / 100000000) := by
  have h := checkLog_sound (w := (671 / 4449)) (n := 12)
    (lo := (303959669 / 1000000000)) (hi := (30395967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1889) = 1/(1889 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30395967 / 100000000) (-303959669 / 1000000000) (Real.log (1889 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (105562631 / 250000000) ≤ -Real.log (512 / 781) ∧
    -Real.log (512 / 781) ≤ (16890021 / 40000000) := by
  have h := checkLog_sound (w := (269 / 1293)) (n := 12)
    (lo := (105562631 / 250000000)) (hi := (16890021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781 / 512) = 1/(512 / 781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (105562631 / 250000000) (16890021 / 40000000) (Real.log (781 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (781 / 512) = -Real.log (512 / 781) := by
    rw [show ((781 / 512) : ℝ) = ((512 / 781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (745263181 / 1000000000) ≤ -Real.log (243 / 512) ∧
    -Real.log (243 / 512) ≤ (745263183 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 499)) (n := 12)
    (lo := (52116001 / 1000000000)) (hi := (26058001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 243) = 1/(243 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-745263183 / 1000000000) (-745263181 / 1000000000) (Real.log (243 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (421481983 / 1000000000) ≤ -Real.log (1280 / 1951) ∧
    -Real.log (1280 / 1951) ≤ (823207 / 1953125) := by
  have h := checkLog_sound (w := (671 / 3231)) (n := 12)
    (lo := (421481983 / 1000000000)) (hi := (823207 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1280) = 1/(1280 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (421481983 / 1000000000) (823207 / 1953125) (Real.log (1951 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1951 / 1280) = -Real.log (1280 / 1951) := by
    rw [show ((1951 / 1280) : ℝ) = ((1280 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23212409 / 31250000) ≤ -Real.log (609 / 1280) ∧
    -Real.log (609 / 1280) ≤ (74279709 / 100000000) := by
  have h := checkLog_sound (w := (31 / 1249)) (n := 12)
    (lo := (12412477 / 250000000)) (hi := (49649909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 609) = 1/(609 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-74279709 / 100000000) (-23212409 / 31250000) (Real.log (609 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79703053 / 250000000) ≤ -Real.log (1000000 / 1375493) ∧
    -Real.log (1000000 / 1375493) ≤ (318812213 / 1000000000) := by
  have h := checkLog_sound (w := (375493 / 2375493)) (n := 12)
    (lo := (79703053 / 250000000)) (hi := (318812213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1375493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1375493 / 1000000) = 1/(1000000 / 1375493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79703053 / 250000000) (318812213 / 1000000000) (Real.log (1375493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1375493 / 1000000) = -Real.log (1000000 / 1375493) := by
    rw [show ((1375493 / 1000000) : ℝ) = ((1000000 / 1375493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23539637 / 50000000) ≤ -Real.log (624507 / 1000000) ∧
    -Real.log (624507 / 1000000) ≤ (470792741 / 1000000000) := by
  have h := checkLog_sound (w := (375493 / 1624507)) (n := 12)
    (lo := (23539637 / 50000000)) (hi := (470792741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 624507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 624507) = 1/(624507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-470792741 / 1000000000) (-23539637 / 50000000) (Real.log (624507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3993011 / 12500000) ≤ -Real.log (500000 / 688179) ∧
    -Real.log (500000 / 688179) ≤ (319440881 / 1000000000) := by
  have h := checkLog_sound (w := (188179 / 1188179)) (n := 12)
    (lo := (3993011 / 12500000)) (hi := (319440881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688179 / 500000) = 1/(500000 / 688179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3993011 / 12500000) (319440881 / 1000000000) (Real.log (688179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (688179 / 500000) = -Real.log (500000 / 688179) := by
    rw [show ((688179 / 500000) : ℝ) = ((500000 / 688179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (472178793 / 1000000000) ≤ -Real.log (311821 / 500000) ∧
    -Real.log (311821 / 500000) ≤ (236089397 / 500000000) := by
  have h := checkLog_sound (w := (188179 / 811821)) (n := 12)
    (lo := (472178793 / 1000000000)) (hi := (236089397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311821) = 1/(311821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-236089397 / 500000000) (-472178793 / 1000000000) (Real.log (311821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (30494483 / 125000000) ≤ -Real.log (15625 / 19942) ∧
    -Real.log (15625 / 19942) ≤ (48791173 / 200000000) := by
  have h := checkLog_sound (w := (4317 / 35567)) (n := 12)
    (lo := (30494483 / 125000000)) (hi := (48791173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19942 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19942 / 15625) = 1/(15625 / 19942) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (30494483 / 125000000) (48791173 / 200000000) (Real.log (19942 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19942 / 15625) = -Real.log (15625 / 19942) := by
    rw [show ((19942 / 15625) : ℝ) = ((15625 / 19942) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64672351 / 200000000) ≤ -Real.log (11308 / 15625) ∧
    -Real.log (11308 / 15625) ≤ (80840439 / 250000000) := by
  have h := checkLog_sound (w := (4317 / 26933)) (n := 12)
    (lo := (64672351 / 200000000)) (hi := (80840439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11308) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11308) = 1/(11308 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-80840439 / 250000000) (-64672351 / 200000000) (Real.log (11308 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (122247391 / 500000000) ≤ -Real.log (62500 / 79811) ∧
    -Real.log (62500 / 79811) ≤ (244494783 / 1000000000) := by
  have h := checkLog_sound (w := (17311 / 142311)) (n := 12)
    (lo := (122247391 / 500000000)) (hi := (244494783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79811 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79811 / 62500) = 1/(62500 / 79811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (122247391 / 500000000) (244494783 / 1000000000) (Real.log (79811 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79811 / 62500) = -Real.log (62500 / 79811) := by
    rw [show ((79811 / 62500) : ℝ) = ((62500 / 79811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162156431 / 500000000) ≤ -Real.log (45189 / 62500) ∧
    -Real.log (45189 / 62500) ≤ (324312863 / 1000000000) := by
  have h := checkLog_sound (w := (17311 / 107689)) (n := 12)
    (lo := (162156431 / 500000000)) (hi := (324312863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45189) = 1/(45189 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-324312863 / 1000000000) (-162156431 / 500000000) (Real.log (45189 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (98700619 / 125000000) ≤ -Real.log (250000000000 / 550631538157) ∧
    -Real.log (250000000000 / 550631538157) ≤ (394802477 / 500000000) := by
  have h := checkLog_sound (w := (50631538157 / 1050631538157)) (n := 12)
    (lo := (24114443 / 250000000)) (hi := (96457773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550631538157 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(550631538157 / 500000000000) = 1/(250000000000 / 550631538157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (98700619 / 125000000) (394802477 / 500000000) (Real.log (550631538157 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (550631538157 / 250000000000) = -Real.log (250000000000 / 550631538157) := by
    rw [show ((550631538157 / 250000000000) : ℝ) = ((250000000000 / 550631538157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (98952459 / 125000000) ≤ -Real.log (100000000000 / 220696810029) ∧
    -Real.log (100000000000 / 220696810029) ≤ (395809837 / 500000000) := by
  have h := checkLog_sound (w := (20696810029 / 420696810029)) (n := 12)
    (lo := (24618123 / 250000000)) (hi := (98472493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220696810029 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(220696810029 / 200000000000) = 1/(100000000000 / 220696810029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (98952459 / 125000000) (395809837 / 500000000) (Real.log (220696810029 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (220696810029 / 100000000000) = -Real.log (100000000000 / 220696810029) := by
    rw [show ((220696810029 / 100000000000) : ℝ) = ((100000000000 / 220696810029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28365881 / 50000000) ≤ -Real.log (500000000000 / 881765122037) ∧
    -Real.log (500000000000 / 881765122037) ≤ (567317621 / 1000000000) := by
  have h := checkLog_sound (w := (381765122037 / 1381765122037)) (n := 12)
    (lo := (28365881 / 50000000)) (hi := (567317621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881765122037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881765122037 / 500000000000) = 1/(500000000000 / 881765122037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (28365881 / 50000000) (567317621 / 1000000000) (Real.log (881765122037 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (881765122037 / 500000000000) = -Real.log (500000000000 / 881765122037) := by
    rw [show ((881765122037 / 500000000000) : ℝ) = ((500000000000 / 881765122037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (113761529 / 200000000) ≤ -Real.log (250000000000 / 441539976543) ∧
    -Real.log (250000000000 / 441539976543) ≤ (284403823 / 500000000) := by
  have h := checkLog_sound (w := (191539976543 / 691539976543)) (n := 12)
    (lo := (113761529 / 200000000)) (hi := (284403823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441539976543 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441539976543 / 250000000000) = 1/(250000000000 / 441539976543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (113761529 / 200000000) (284403823 / 500000000) (Real.log (441539976543 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (441539976543 / 250000000000) = -Real.log (250000000000 / 441539976543) := by
    rw [show ((441539976543 / 250000000000) : ℝ) = ((250000000000 / 441539976543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0271

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0272Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0272
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

theorem reflection_log_1_neg : (58196107 / 250000000) ≤ -Real.log (2560 / 3231) ∧
    -Real.log (2560 / 3231) ≤ (232784429 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 5791)) (n := 12)
    (lo := (58196107 / 250000000)) (hi := (232784429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3231 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3231 / 2560) = 1/(2560 / 3231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58196107 / 250000000) (232784429 / 1000000000) (Real.log (3231 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3231 / 2560) = -Real.log (2560 / 3231) := by
    rw [show ((3231 / 2560) : ℝ) = ((2560 / 3231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303959669 / 1000000000) ≤ -Real.log (1889 / 2560) ∧
    -Real.log (1889 / 2560) ≤ (30395967 / 100000000) := by
  have h := checkLog_sound (w := (671 / 4449)) (n := 12)
    (lo := (303959669 / 1000000000)) (hi := (30395967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1889) = 1/(1889 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30395967 / 100000000) (-303959669 / 1000000000) (Real.log (1889 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (232320067 / 1000000000) ≤ -Real.log (5120 / 6459) ∧
    -Real.log (5120 / 6459) ≤ (58080017 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 11579)) (n := 12)
    (lo := (232320067 / 1000000000)) (hi := (58080017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6459 / 5120) = 1/(5120 / 6459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (232320067 / 1000000000) (58080017 / 250000000) (Real.log (6459 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6459 / 5120) = -Real.log (5120 / 6459) := by
    rw [show ((6459 / 5120) : ℝ) = ((5120 / 6459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (151582957 / 500000000) ≤ -Real.log (3781 / 5120) ∧
    -Real.log (3781 / 5120) ≤ (60633183 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 8901)) (n := 12)
    (lo := (151582957 / 500000000)) (hi := (60633183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3781) = 1/(3781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60633183 / 200000000) (-151582957 / 500000000) (Real.log (3781 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (421481983 / 1000000000) ≤ -Real.log (1280 / 1951) ∧
    -Real.log (1280 / 1951) ≤ (823207 / 1953125) := by
  have h := checkLog_sound (w := (671 / 3231)) (n := 12)
    (lo := (421481983 / 1000000000)) (hi := (823207 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1280) = 1/(1280 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (421481983 / 1000000000) (823207 / 1953125) (Real.log (1951 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1951 / 1280) = -Real.log (1280 / 1951) := by
    rw [show ((1951 / 1280) : ℝ) = ((1280 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23212409 / 31250000) ≤ -Real.log (609 / 1280) ∧
    -Real.log (609 / 1280) ≤ (74279709 / 100000000) := by
  have h := checkLog_sound (w := (31 / 1249)) (n := 12)
    (lo := (12412477 / 250000000)) (hi := (49649909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 609) = 1/(609 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-74279709 / 100000000) (-23212409 / 31250000) (Real.log (609 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (420712851 / 1000000000) ≤ -Real.log (2560 / 3899) ∧
    -Real.log (2560 / 3899) ≤ (105178213 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 6459)) (n := 12)
    (lo := (420712851 / 1000000000)) (hi := (105178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3899 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3899 / 2560) = 1/(2560 / 3899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (420712851 / 1000000000) (105178213 / 250000000) (Real.log (3899 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3899 / 2560) = -Real.log (2560 / 3899) := by
    rw [show ((3899 / 2560) : ℝ) = ((2560 / 3899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (370168531 / 500000000) ≤ -Real.log (1221 / 2560) ∧
    -Real.log (1221 / 2560) ≤ (92542133 / 125000000) := by
  have h := checkLog_sound (w := (59 / 2501)) (n := 12)
    (lo := (23594941 / 500000000)) (hi := (47189883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1221) = 1/(1221 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-92542133 / 125000000) (-370168531 / 500000000) (Real.log (1221 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79545969 / 250000000) ≤ -Real.log (1000000 / 1374629) ∧
    -Real.log (1000000 / 1374629) ≤ (318183877 / 1000000000) := by
  have h := checkLog_sound (w := (374629 / 2374629)) (n := 12)
    (lo := (79545969 / 250000000)) (hi := (318183877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374629 / 1000000) = 1/(1000000 / 1374629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79545969 / 250000000) (318183877 / 1000000000) (Real.log (1374629 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1374629 / 1000000) = -Real.log (1000000 / 1374629) := by
    rw [show ((1374629 / 1000000) : ℝ) = ((1000000 / 1374629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93882041 / 200000000) ≤ -Real.log (625371 / 1000000) ∧
    -Real.log (625371 / 1000000) ≤ (234705103 / 500000000) := by
  have h := checkLog_sound (w := (374629 / 1625371)) (n := 12)
    (lo := (93882041 / 200000000)) (hi := (234705103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625371) = 1/(625371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-234705103 / 500000000) (-93882041 / 200000000) (Real.log (625371 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318812939 / 1000000000) ≤ -Real.log (500000 / 687747) ∧
    -Real.log (500000 / 687747) ≤ (15940647 / 50000000) := by
  have h := checkLog_sound (w := (187747 / 1187747)) (n := 12)
    (lo := (318812939 / 1000000000)) (hi := (15940647 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687747 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687747 / 500000) = 1/(500000 / 687747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318812939 / 1000000000) (15940647 / 50000000) (Real.log (687747 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (687747 / 500000) = -Real.log (500000 / 687747) := by
    rw [show ((687747 / 500000) : ℝ) = ((500000 / 687747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (470794341 / 1000000000) ≤ -Real.log (312253 / 500000) ∧
    -Real.log (312253 / 500000) ≤ (235397171 / 500000000) := by
  have h := checkLog_sound (w := (187747 / 812253)) (n := 12)
    (lo := (470794341 / 1000000000)) (hi := (235397171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 312253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 312253) = 1/(312253 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-235397171 / 500000000) (-470794341 / 1000000000) (Real.log (312253 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1521359 / 6250000) ≤ -Real.log (1000000 / 1275601) ∧
    -Real.log (1000000 / 1275601) ≤ (243417441 / 1000000000) := by
  have h := checkLog_sound (w := (275601 / 2275601)) (n := 12)
    (lo := (1521359 / 6250000)) (hi := (243417441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275601 / 1000000) = 1/(1000000 / 1275601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1521359 / 6250000) (243417441 / 1000000000) (Real.log (1275601 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1275601 / 1000000) = -Real.log (1000000 / 1275601) := by
    rw [show ((1275601 / 1000000) : ℝ) = ((1000000 / 1275601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (322412933 / 1000000000) ≤ -Real.log (724399 / 1000000) ∧
    -Real.log (724399 / 1000000) ≤ (161206467 / 500000000) := by
  have h := checkLog_sound (w := (275601 / 1724399)) (n := 12)
    (lo := (322412933 / 1000000000)) (hi := (161206467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724399) = 1/(724399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-161206467 / 500000000) (-322412933 / 1000000000) (Real.log (724399 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30494581 / 125000000) ≤ -Real.log (1000000 / 1276289) ∧
    -Real.log (1000000 / 1276289) ≤ (243956649 / 1000000000) := by
  have h := checkLog_sound (w := (276289 / 2276289)) (n := 12)
    (lo := (30494581 / 125000000)) (hi := (243956649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276289 / 1000000) = 1/(1000000 / 1276289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30494581 / 125000000) (243956649 / 1000000000) (Real.log (1276289 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1276289 / 1000000) = -Real.log (1000000 / 1276289) := by
    rw [show ((1276289 / 1000000) : ℝ) = ((1000000 / 1276289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (323363137 / 1000000000) ≤ -Real.log (723711 / 1000000) ∧
    -Real.log (723711 / 1000000) ≤ (161681569 / 500000000) := by
  have h := checkLog_sound (w := (276289 / 1723711)) (n := 12)
    (lo := (323363137 / 1000000000)) (hi := (161681569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723711) = 1/(723711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-161681569 / 500000000) (-323363137 / 1000000000) (Real.log (723711 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (787594081 / 1000000000) ≤ -Real.log (500000000000 / 1099050803443) ∧
    -Real.log (500000000000 / 1099050803443) ≤ (787594083 / 1000000000) := by
  have h := checkLog_sound (w := (99050803443 / 2099050803443)) (n := 12)
    (lo := (94446901 / 1000000000)) (hi := (47223451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099050803443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099050803443 / 1000000000000) = 1/(500000000000 / 1099050803443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (787594081 / 1000000000) (787594083 / 1000000000) (Real.log (1099050803443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1099050803443 / 500000000000) = -Real.log (500000000000 / 1099050803443) := by
    rw [show ((1099050803443 / 500000000000) : ℝ) = ((500000000000 / 1099050803443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9870091 / 12500000) ≤ -Real.log (500000000000 / 1101265640363) ∧
    -Real.log (500000000000 / 1101265640363) ≤ (394803641 / 500000000) := by
  have h := checkLog_sound (w := (101265640363 / 2101265640363)) (n := 12)
    (lo := (964601 / 10000000)) (hi := (96460101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101265640363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101265640363 / 1000000000000) = 1/(500000000000 / 1101265640363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9870091 / 12500000) (394803641 / 500000000) (Real.log (1101265640363 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1101265640363 / 500000000000) = -Real.log (500000000000 / 1101265640363) := by
    rw [show ((1101265640363 / 500000000000) : ℝ) = ((500000000000 / 1101265640363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (565830373 / 1000000000) ≤ -Real.log (500000000000 / 880454694167) ∧
    -Real.log (500000000000 / 880454694167) ≤ (282915187 / 500000000) := by
  have h := checkLog_sound (w := (380454694167 / 1380454694167)) (n := 12)
    (lo := (565830373 / 1000000000)) (hi := (282915187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880454694167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880454694167 / 500000000000) = 1/(500000000000 / 880454694167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (565830373 / 1000000000) (282915187 / 500000000) (Real.log (880454694167 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (880454694167 / 500000000000) = -Real.log (500000000000 / 880454694167) := by
    rw [show ((880454694167 / 500000000000) : ℝ) = ((500000000000 / 880454694167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (113463957 / 200000000) ≤ -Real.log (100000000000 / 176353406263) ∧
    -Real.log (100000000000 / 176353406263) ≤ (283659893 / 500000000) := by
  have h := checkLog_sound (w := (76353406263 / 276353406263)) (n := 12)
    (lo := (113463957 / 200000000)) (hi := (283659893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176353406263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176353406263 / 100000000000) = 1/(100000000000 / 176353406263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (113463957 / 200000000) (283659893 / 500000000) (Real.log (176353406263 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (176353406263 / 100000000000) = -Real.log (100000000000 / 176353406263) := by
    rw [show ((176353406263 / 100000000000) : ℝ) = ((100000000000 / 176353406263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0272

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0273Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0273
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

theorem reflection_log_1_neg : (232320067 / 1000000000) ≤ -Real.log (5120 / 6459) ∧
    -Real.log (5120 / 6459) ≤ (58080017 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 11579)) (n := 12)
    (lo := (232320067 / 1000000000)) (hi := (58080017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6459 / 5120) = 1/(5120 / 6459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (232320067 / 1000000000) (58080017 / 250000000) (Real.log (6459 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6459 / 5120) = -Real.log (5120 / 6459) := by
    rw [show ((6459 / 5120) : ℝ) = ((5120 / 6459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (151582957 / 500000000) ≤ -Real.log (3781 / 5120) ∧
    -Real.log (3781 / 5120) ≤ (60633183 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 8901)) (n := 12)
    (lo := (151582957 / 500000000)) (hi := (60633183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3781) = 1/(3781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60633183 / 200000000) (-151582957 / 500000000) (Real.log (3781 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (231855491 / 1000000000) ≤ -Real.log (640 / 807) ∧
    -Real.log (640 / 807) ≤ (57963873 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1447)) (n := 12)
    (lo := (231855491 / 1000000000)) (hi := (57963873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 640) = 1/(640 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (231855491 / 1000000000) (57963873 / 250000000) (Real.log (807 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (807 / 640) = -Real.log (640 / 807) := by
    rw [show ((807 / 640) : ℝ) = ((640 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302372787 / 1000000000) ≤ -Real.log (473 / 640) ∧
    -Real.log (473 / 640) ≤ (75593197 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1113)) (n := 12)
    (lo := (302372787 / 1000000000)) (hi := (75593197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 473) = 1/(473 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-75593197 / 250000000) (-302372787 / 1000000000) (Real.log (473 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (420712851 / 1000000000) ≤ -Real.log (2560 / 3899) ∧
    -Real.log (2560 / 3899) ≤ (105178213 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 6459)) (n := 12)
    (lo := (420712851 / 1000000000)) (hi := (105178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3899 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3899 / 2560) = 1/(2560 / 3899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (420712851 / 1000000000) (105178213 / 250000000) (Real.log (3899 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3899 / 2560) = -Real.log (2560 / 3899) := by
    rw [show ((3899 / 2560) : ℝ) = ((2560 / 3899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (370168531 / 500000000) ≤ -Real.log (1221 / 2560) ∧
    -Real.log (1221 / 2560) ≤ (92542133 / 125000000) := by
  have h := checkLog_sound (w := (59 / 2501)) (n := 12)
    (lo := (23594941 / 500000000)) (hi := (47189883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1221) = 1/(1221 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-92542133 / 125000000) (-370168531 / 500000000) (Real.log (1221 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (419943127 / 1000000000) ≤ -Real.log (320 / 487) ∧
    -Real.log (320 / 487) ≤ (52492891 / 125000000) := by
  have h := checkLog_sound (w := (167 / 807)) (n := 12)
    (lo := (419943127 / 1000000000)) (hi := (52492891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487 / 320) = 1/(320 / 487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (419943127 / 1000000000) (52492891 / 125000000) (Real.log (487 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (487 / 320) = -Real.log (320 / 487) := by
    rw [show ((487 / 320) : ℝ) = ((320 / 487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (737883073 / 1000000000) ≤ -Real.log (153 / 320) ∧
    -Real.log (153 / 320) ≤ (29515323 / 40000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 153) = 1/(153 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29515323 / 40000000) (-737883073 / 1000000000) (Real.log (153 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63511029 / 200000000) ≤ -Real.log (200000 / 274753) ∧
    -Real.log (200000 / 274753) ≤ (158777573 / 500000000) := by
  have h := checkLog_sound (w := (74753 / 474753)) (n := 12)
    (lo := (63511029 / 200000000)) (hi := (158777573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274753 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274753 / 200000) = 1/(200000 / 274753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63511029 / 200000000) (158777573 / 500000000) (Real.log (274753 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (274753 / 200000) = -Real.log (200000 / 274753) := by
    rw [show ((274753 / 200000) : ℝ) = ((200000 / 274753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (234014789 / 500000000) ≤ -Real.log (125247 / 200000) ∧
    -Real.log (125247 / 200000) ≤ (468029579 / 1000000000) := by
  have h := checkLog_sound (w := (74753 / 325247)) (n := 12)
    (lo := (234014789 / 500000000)) (hi := (468029579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125247) = 1/(125247 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-468029579 / 1000000000) (-234014789 / 500000000) (Real.log (125247 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318184603 / 1000000000) ≤ -Real.log (100000 / 137463) ∧
    -Real.log (100000 / 137463) ≤ (79546151 / 250000000) := by
  have h := checkLog_sound (w := (37463 / 237463)) (n := 12)
    (lo := (318184603 / 1000000000)) (hi := (79546151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137463 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137463 / 100000) = 1/(100000 / 137463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318184603 / 1000000000) (79546151 / 250000000) (Real.log (137463 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (137463 / 100000) = -Real.log (100000 / 137463) := by
    rw [show ((137463 / 100000) : ℝ) = ((100000 / 137463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (117352951 / 250000000) ≤ -Real.log (62537 / 100000) ∧
    -Real.log (62537 / 100000) ≤ (93882361 / 200000000) := by
  have h := checkLog_sound (w := (37463 / 162537)) (n := 12)
    (lo := (117352951 / 250000000)) (hi := (93882361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62537) = 1/(62537 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93882361 / 200000000) (-117352951 / 250000000) (Real.log (62537 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9715149 / 40000000) ≤ -Real.log (500000 / 637457) ∧
    -Real.log (500000 / 637457) ≤ (121439363 / 500000000) := by
  have h := checkLog_sound (w := (137457 / 1137457)) (n := 12)
    (lo := (9715149 / 40000000)) (hi := (121439363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637457 / 500000) = 1/(500000 / 637457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9715149 / 40000000) (121439363 / 500000000) (Real.log (637457 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (637457 / 500000) = -Real.log (500000 / 637457) := by
    rw [show ((637457 / 500000) : ℝ) = ((500000 / 637457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (32146501 / 100000000) ≤ -Real.log (362543 / 500000) ∧
    -Real.log (362543 / 500000) ≤ (321465011 / 1000000000) := by
  have h := checkLog_sound (w := (137457 / 862543)) (n := 12)
    (lo := (32146501 / 100000000)) (hi := (321465011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362543) = 1/(362543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-321465011 / 1000000000) (-32146501 / 100000000) (Real.log (362543 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (15213639 / 62500000) ≤ -Real.log (500000 / 637801) ∧
    -Real.log (500000 / 637801) ≤ (9736729 / 40000000) := by
  have h := checkLog_sound (w := (137801 / 1137801)) (n := 12)
    (lo := (15213639 / 62500000)) (hi := (9736729 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637801 / 500000) = 1/(500000 / 637801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15213639 / 62500000) (9736729 / 40000000) (Real.log (637801 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (637801 / 500000) = -Real.log (500000 / 637801) := by
    rw [show ((637801 / 500000) : ℝ) = ((500000 / 637801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (322414313 / 1000000000) ≤ -Real.log (362199 / 500000) ∧
    -Real.log (362199 / 500000) ≤ (161207157 / 500000000) := by
  have h := checkLog_sound (w := (137801 / 862199)) (n := 12)
    (lo := (322414313 / 1000000000)) (hi := (161207157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362199) = 1/(362199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-161207157 / 500000000) (-322414313 / 1000000000) (Real.log (362199 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (196396181 / 250000000) ≤ -Real.log (500000000000 / 1096844635001) ∧
    -Real.log (500000000000 / 1096844635001) ≤ (392792363 / 500000000) := by
  have h := checkLog_sound (w := (96844635001 / 2096844635001)) (n := 12)
    (lo := (11554693 / 125000000)) (hi := (18487509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096844635001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096844635001 / 1000000000000) = 1/(500000000000 / 1096844635001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (196396181 / 250000000) (392792363 / 500000000) (Real.log (1096844635001 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1096844635001 / 500000000000) = -Real.log (500000000000 / 1096844635001) := by
    rw [show ((1096844635001 / 500000000000) : ℝ) = ((500000000000 / 1096844635001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (787596407 / 1000000000) ≤ -Real.log (500000000000 / 1099053360411) ∧
    -Real.log (500000000000 / 1099053360411) ≤ (787596409 / 1000000000) := by
  have h := checkLog_sound (w := (99053360411 / 2099053360411)) (n := 12)
    (lo := (94449227 / 1000000000)) (hi := (23612307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099053360411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099053360411 / 1000000000000) = 1/(500000000000 / 1099053360411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (787596407 / 1000000000) (787596409 / 1000000000) (Real.log (1099053360411 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1099053360411 / 500000000000) = -Real.log (500000000000 / 1099053360411) := by
    rw [show ((1099053360411 / 500000000000) : ℝ) = ((500000000000 / 1099053360411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112868747 / 200000000) ≤ -Real.log (500000000000 / 879146749489) ∧
    -Real.log (500000000000 / 879146749489) ≤ (70542967 / 125000000) := by
  have h := checkLog_sound (w := (379146749489 / 1379146749489)) (n := 12)
    (lo := (112868747 / 200000000)) (hi := (70542967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879146749489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879146749489 / 500000000000) = 1/(500000000000 / 879146749489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112868747 / 200000000) (70542967 / 125000000) (Real.log (879146749489 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (879146749489 / 500000000000) = -Real.log (500000000000 / 879146749489) := by
    rw [show ((879146749489 / 500000000000) : ℝ) = ((500000000000 / 879146749489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (565832537 / 1000000000) ≤ -Real.log (20000000000 / 35218263993) ∧
    -Real.log (20000000000 / 35218263993) ≤ (282916269 / 500000000) := by
  have h := checkLog_sound (w := (15218263993 / 55218263993)) (n := 12)
    (lo := (565832537 / 1000000000)) (hi := (282916269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35218263993 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35218263993 / 20000000000) = 1/(20000000000 / 35218263993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (565832537 / 1000000000) (282916269 / 500000000) (Real.log (35218263993 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (35218263993 / 20000000000) = -Real.log (20000000000 / 35218263993) := by
    rw [show ((35218263993 / 20000000000) : ℝ) = ((20000000000 / 35218263993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0273

end


