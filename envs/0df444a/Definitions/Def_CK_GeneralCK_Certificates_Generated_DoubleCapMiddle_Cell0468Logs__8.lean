-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0468Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0468Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:12:04.503322+00:00
-- url     : https://prove2.me/theorems/9cb3e336-94af-46b4-a93d-3f94abe1ac2c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0468Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0469Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0468Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0469Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0470Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0471Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0472Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0473Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0474Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0475Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0468Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0469Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0470Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0471Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0472Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0473Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0474Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0475Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0468Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0469Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0470Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0471Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0472Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0473Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0474Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0475Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0468Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0469Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0470Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0471Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0472Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0473Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0474Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0475Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0468Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0468
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

theorem reflection_log_1_neg : (11486583 / 62500000) ≤ -Real.log (5120 / 6153) ∧
    -Real.log (5120 / 6153) ≤ (183785329 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 11273)) (n := 12)
    (lo := (11486583 / 62500000)) (hi := (183785329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6153 / 5120) = 1/(5120 / 6153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11486583 / 62500000) (183785329 / 1000000000) (Real.log (6153 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6153 / 5120) = -Real.log (5120 / 6153) := by
    rw [show ((6153 / 5120) : ℝ) = ((5120 / 6153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112671617 / 500000000) ≤ -Real.log (4087 / 5120) ∧
    -Real.log (4087 / 5120) ≤ (45068647 / 200000000) := by
  have h := checkLog_sound (w := (1033 / 9207)) (n := 12)
    (lo := (112671617 / 500000000)) (hi := (45068647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4087) = 1/(4087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45068647 / 200000000) (-112671617 / 500000000) (Real.log (4087 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (183663429 / 1000000000) ≤ -Real.log (20480 / 24609) ∧
    -Real.log (20480 / 24609) ≤ (18366343 / 100000000) := by
  have h := checkLog_sound (w := (4129 / 45089)) (n := 12)
    (lo := (183663429 / 1000000000)) (hi := (18366343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24609 / 20480) = 1/(20480 / 24609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (183663429 / 1000000000) (18366343 / 100000000) (Real.log (24609 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24609 / 20480) = -Real.log (20480 / 24609) := by
    rw [show ((24609 / 20480) : ℝ) = ((20480 / 24609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112579871 / 500000000) ≤ -Real.log (16351 / 20480) ∧
    -Real.log (16351 / 20480) ≤ (225159743 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 36831)) (n := 12)
    (lo := (112579871 / 500000000)) (hi := (225159743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16351) = 1/(16351 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-225159743 / 1000000000) (-112579871 / 500000000) (Real.log (16351 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (338980249 / 1000000000) ≤ -Real.log (2560 / 3593) ∧
    -Real.log (2560 / 3593) ≤ (1355921 / 4000000) := by
  have h := checkLog_sound (w := (1033 / 6153)) (n := 12)
    (lo := (338980249 / 1000000000)) (hi := (1355921 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3593 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3593 / 2560) = 1/(2560 / 3593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (338980249 / 1000000000) (1355921 / 4000000) (Real.log (3593 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3593 / 2560) = -Real.log (2560 / 3593) := by
    rw [show ((3593 / 2560) : ℝ) = ((2560 / 3593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64587779 / 125000000) ≤ -Real.log (1527 / 2560) ∧
    -Real.log (1527 / 2560) ≤ (516702233 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 4087)) (n := 12)
    (lo := (64587779 / 125000000)) (hi := (516702233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1527) = 1/(1527 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-516702233 / 1000000000) (-64587779 / 125000000) (Real.log (1527 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10586609 / 31250000) ≤ -Real.log (10240 / 14369) ∧
    -Real.log (10240 / 14369) ≤ (338771489 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 24609)) (n := 12)
    (lo := (10586609 / 31250000)) (hi := (338771489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14369 / 10240) = 1/(10240 / 14369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10586609 / 31250000) (338771489 / 1000000000) (Real.log (14369 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14369 / 10240) = -Real.log (10240 / 14369) := by
    rw [show ((14369 / 10240) : ℝ) = ((10240 / 14369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (516211193 / 1000000000) ≤ -Real.log (6111 / 10240) ∧
    -Real.log (6111 / 10240) ≤ (258105597 / 500000000) := by
  have h := checkLog_sound (w := (4129 / 16351)) (n := 12)
    (lo := (516211193 / 1000000000)) (hi := (258105597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6111) = 1/(6111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258105597 / 500000000) (-516211193 / 1000000000) (Real.log (6111 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31558179 / 125000000) ≤ -Real.log (200000 / 257439) ∧
    -Real.log (200000 / 257439) ≤ (252465433 / 1000000000) := by
  have h := checkLog_sound (w := (57439 / 457439)) (n := 12)
    (lo := (31558179 / 125000000)) (hi := (252465433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257439 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257439 / 200000) = 1/(200000 / 257439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31558179 / 125000000) (252465433 / 1000000000) (Real.log (257439 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (257439 / 200000) = -Real.log (200000 / 257439) := by
    rw [show ((257439 / 200000) : ℝ) = ((200000 / 257439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84636847 / 250000000) ≤ -Real.log (142561 / 200000) ∧
    -Real.log (142561 / 200000) ≤ (338547389 / 1000000000) := by
  have h := checkLog_sound (w := (57439 / 342561)) (n := 12)
    (lo := (84636847 / 250000000)) (hi := (338547389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142561) = 1/(142561 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-338547389 / 1000000000) (-84636847 / 250000000) (Real.log (142561 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126315447 / 500000000) ≤ -Real.log (62500 / 80463) ∧
    -Real.log (62500 / 80463) ≤ (50526179 / 200000000) := by
  have h := checkLog_sound (w := (17963 / 142963)) (n := 12)
    (lo := (126315447 / 500000000)) (hi := (50526179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80463 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80463 / 62500) = 1/(62500 / 80463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126315447 / 500000000) (50526179 / 200000000) (Real.log (80463 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80463 / 62500) = -Real.log (62500 / 80463) := by
    rw [show ((80463 / 62500) : ℝ) = ((62500 / 80463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84711563 / 250000000) ≤ -Real.log (44537 / 62500) ∧
    -Real.log (44537 / 62500) ≤ (338846253 / 1000000000) := by
  have h := checkLog_sound (w := (17963 / 107037)) (n := 12)
    (lo := (84711563 / 250000000)) (hi := (338846253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44537) = 1/(44537 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-338846253 / 1000000000) (-84711563 / 250000000) (Real.log (44537 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188820393 / 1000000000) ≤ -Real.log (62500 / 75489) ∧
    -Real.log (62500 / 75489) ≤ (94410197 / 500000000) := by
  have h := checkLog_sound (w := (12989 / 137989)) (n := 12)
    (lo := (188820393 / 1000000000)) (hi := (94410197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75489 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75489 / 62500) = 1/(62500 / 75489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188820393 / 1000000000) (94410197 / 500000000) (Real.log (75489 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75489 / 62500) = -Real.log (62500 / 75489) := by
    rw [show ((75489 / 62500) : ℝ) = ((62500 / 75489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (232971689 / 1000000000) ≤ -Real.log (49511 / 62500) ∧
    -Real.log (49511 / 62500) ≤ (23297169 / 100000000) := by
  have h := checkLog_sound (w := (12989 / 112011)) (n := 12)
    (lo := (232971689 / 1000000000)) (hi := (23297169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49511) = 1/(49511 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-23297169 / 100000000) (-232971689 / 1000000000) (Real.log (49511 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18895451 / 100000000) ≤ -Real.log (500000 / 603993) ∧
    -Real.log (500000 / 603993) ≤ (188954511 / 1000000000) := by
  have h := checkLog_sound (w := (103993 / 1103993)) (n := 12)
    (lo := (18895451 / 100000000)) (hi := (188954511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603993 / 500000) = 1/(500000 / 603993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18895451 / 100000000) (188954511 / 1000000000) (Real.log (603993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603993 / 500000) = -Real.log (500000 / 603993) := by
    rw [show ((603993 / 500000) : ℝ) = ((500000 / 603993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23317621 / 100000000) ≤ -Real.log (396007 / 500000) ∧
    -Real.log (396007 / 500000) ≤ (233176211 / 1000000000) := by
  have h := checkLog_sound (w := (103993 / 896007)) (n := 12)
    (lo := (23317621 / 100000000)) (hi := (233176211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396007) = 1/(396007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-233176211 / 1000000000) (-23317621 / 100000000) (Real.log (396007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (29550641 / 50000000) ≤ -Real.log (250000000000 / 451454114379) ∧
    -Real.log (250000000000 / 451454114379) ≤ (591012821 / 1000000000) := by
  have h := checkLog_sound (w := (201454114379 / 701454114379)) (n := 12)
    (lo := (29550641 / 50000000)) (hi := (591012821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451454114379 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451454114379 / 250000000000) = 1/(250000000000 / 451454114379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (29550641 / 50000000) (591012821 / 1000000000) (Real.log (451454114379 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (451454114379 / 250000000000) = -Real.log (250000000000 / 451454114379) := by
    rw [show ((451454114379 / 250000000000) : ℝ) = ((250000000000 / 451454114379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (591477147 / 1000000000) ≤ -Real.log (100000000000 / 180665514067) ∧
    -Real.log (100000000000 / 180665514067) ≤ (147869287 / 250000000) := by
  have h := checkLog_sound (w := (80665514067 / 280665514067)) (n := 12)
    (lo := (591477147 / 1000000000)) (hi := (147869287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180665514067 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180665514067 / 100000000000) = 1/(100000000000 / 180665514067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (591477147 / 1000000000) (147869287 / 250000000) (Real.log (180665514067 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (180665514067 / 100000000000) = -Real.log (100000000000 / 180665514067) := by
    rw [show ((180665514067 / 100000000000) : ℝ) = ((100000000000 / 180665514067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421792083 / 1000000000) ≤ -Real.log (10000000000 / 15246914827) ∧
    -Real.log (10000000000 / 15246914827) ≤ (105448021 / 250000000) := by
  have h := checkLog_sound (w := (5246914827 / 25246914827)) (n := 12)
    (lo := (421792083 / 1000000000)) (hi := (105448021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15246914827 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15246914827 / 10000000000) = 1/(10000000000 / 15246914827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421792083 / 1000000000) (105448021 / 250000000) (Real.log (15246914827 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15246914827 / 10000000000) = -Real.log (10000000000 / 15246914827) := by
    rw [show ((15246914827 / 10000000000) : ℝ) = ((10000000000 / 15246914827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2638317 / 6250000) ≤ -Real.log (50000000000 / 76260394387) ∧
    -Real.log (50000000000 / 76260394387) ≤ (422130721 / 1000000000) := by
  have h := checkLog_sound (w := (26260394387 / 126260394387)) (n := 12)
    (lo := (2638317 / 6250000)) (hi := (422130721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76260394387 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76260394387 / 50000000000) = 1/(50000000000 / 76260394387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2638317 / 6250000) (422130721 / 1000000000) (Real.log (76260394387 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76260394387 / 50000000000) = -Real.log (50000000000 / 76260394387) := by
    rw [show ((76260394387 / 50000000000) : ℝ) = ((50000000000 / 76260394387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0468

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0469Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0469
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

theorem reflection_log_1_neg : (183663429 / 1000000000) ≤ -Real.log (20480 / 24609) ∧
    -Real.log (20480 / 24609) ≤ (18366343 / 100000000) := by
  have h := checkLog_sound (w := (4129 / 45089)) (n := 12)
    (lo := (183663429 / 1000000000)) (hi := (18366343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24609 / 20480) = 1/(20480 / 24609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (183663429 / 1000000000) (18366343 / 100000000) (Real.log (24609 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24609 / 20480) = -Real.log (20480 / 24609) := by
    rw [show ((24609 / 20480) : ℝ) = ((20480 / 24609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112579871 / 500000000) ≤ -Real.log (16351 / 20480) ∧
    -Real.log (16351 / 20480) ≤ (225159743 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 36831)) (n := 12)
    (lo := (112579871 / 500000000)) (hi := (225159743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16351) = 1/(16351 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-225159743 / 1000000000) (-112579871 / 500000000) (Real.log (16351 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (36708303 / 200000000) ≤ -Real.log (10240 / 12303) ∧
    -Real.log (10240 / 12303) ≤ (45885379 / 250000000) := by
  have h := checkLog_sound (w := (2063 / 22543)) (n := 12)
    (lo := (36708303 / 200000000)) (hi := (45885379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12303 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12303 / 10240) = 1/(10240 / 12303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (36708303 / 200000000) (45885379 / 250000000) (Real.log (12303 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12303 / 10240) = -Real.log (10240 / 12303) := by
    rw [show ((12303 / 10240) : ℝ) = ((10240 / 12303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56244071 / 250000000) ≤ -Real.log (8177 / 10240) ∧
    -Real.log (8177 / 10240) ≤ (44995257 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 18417)) (n := 12)
    (lo := (56244071 / 250000000)) (hi := (44995257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8177) = 1/(8177 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44995257 / 200000000) (-56244071 / 250000000) (Real.log (8177 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10586609 / 31250000) ≤ -Real.log (10240 / 14369) ∧
    -Real.log (10240 / 14369) ≤ (338771489 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 24609)) (n := 12)
    (lo := (10586609 / 31250000)) (hi := (338771489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14369 / 10240) = 1/(10240 / 14369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10586609 / 31250000) (338771489 / 1000000000) (Real.log (14369 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14369 / 10240) = -Real.log (10240 / 14369) := by
    rw [show ((14369 / 10240) : ℝ) = ((10240 / 14369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (516211193 / 1000000000) ≤ -Real.log (6111 / 10240) ∧
    -Real.log (6111 / 10240) ≤ (258105597 / 500000000) := by
  have h := checkLog_sound (w := (4129 / 16351)) (n := 12)
    (lo := (516211193 / 1000000000)) (hi := (258105597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6111) = 1/(6111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258105597 / 500000000) (-516211193 / 1000000000) (Real.log (6111 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84640671 / 250000000) ≤ -Real.log (5120 / 7183) ∧
    -Real.log (5120 / 7183) ≤ (67712537 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 12303)) (n := 12)
    (lo := (84640671 / 250000000)) (hi := (67712537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7183 / 5120) = 1/(5120 / 7183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84640671 / 250000000) (67712537 / 200000000) (Real.log (7183 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7183 / 5120) = -Real.log (5120 / 7183) := by
    rw [show ((7183 / 5120) : ℝ) = ((5120 / 7183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128930099 / 250000000) ≤ -Real.log (3057 / 5120) ∧
    -Real.log (3057 / 5120) ≤ (515720397 / 1000000000) := by
  have h := checkLog_sound (w := (2063 / 8177)) (n := 12)
    (lo := (128930099 / 250000000)) (hi := (515720397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3057) = 1/(3057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-515720397 / 1000000000) (-128930099 / 250000000) (Real.log (3057 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252300719 / 1000000000) ≤ -Real.log (1000000 / 1286983) ∧
    -Real.log (1000000 / 1286983) ≤ (3153759 / 12500000) := by
  have h := checkLog_sound (w := (286983 / 2286983)) (n := 12)
    (lo := (252300719 / 1000000000)) (hi := (3153759 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286983 / 1000000) = 1/(1000000 / 1286983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252300719 / 1000000000) (3153759 / 12500000) (Real.log (1286983 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286983 / 1000000) = -Real.log (1000000 / 1286983) := by
    rw [show ((1286983 / 1000000) : ℝ) = ((1000000 / 1286983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67650003 / 200000000) ≤ -Real.log (713017 / 1000000) ∧
    -Real.log (713017 / 1000000) ≤ (10570313 / 31250000) := by
  have h := checkLog_sound (w := (286983 / 1713017)) (n := 12)
    (lo := (67650003 / 200000000)) (hi := (10570313 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713017) = 1/(713017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10570313 / 31250000) (-67650003 / 200000000) (Real.log (713017 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (252466209 / 1000000000) ≤ -Real.log (250000 / 321799) ∧
    -Real.log (250000 / 321799) ≤ (25246621 / 100000000) := by
  have h := checkLog_sound (w := (71799 / 571799)) (n := 12)
    (lo := (252466209 / 1000000000)) (hi := (25246621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321799 / 250000) = 1/(250000 / 321799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (252466209 / 1000000000) (25246621 / 100000000) (Real.log (321799 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (321799 / 250000) = -Real.log (250000 / 321799) := by
    rw [show ((321799 / 250000) : ℝ) = ((250000 / 321799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (338548791 / 1000000000) ≤ -Real.log (178201 / 250000) ∧
    -Real.log (178201 / 250000) ≤ (42318599 / 125000000) := by
  have h := checkLog_sound (w := (71799 / 428201)) (n := 12)
    (lo := (338548791 / 1000000000)) (hi := (42318599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178201) = 1/(178201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42318599 / 125000000) (-338548791 / 1000000000) (Real.log (178201 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37737583 / 200000000) ≤ -Real.log (62500 / 75479) ∧
    -Real.log (62500 / 75479) ≤ (47171979 / 250000000) := by
  have h := checkLog_sound (w := (12979 / 137979)) (n := 12)
    (lo := (37737583 / 200000000)) (hi := (47171979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75479 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75479 / 62500) = 1/(62500 / 75479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37737583 / 200000000) (47171979 / 250000000) (Real.log (75479 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75479 / 62500) = -Real.log (62500 / 75479) := by
    rw [show ((75479 / 62500) : ℝ) = ((62500 / 75479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (116384867 / 500000000) ≤ -Real.log (49521 / 62500) ∧
    -Real.log (49521 / 62500) ≤ (46553947 / 200000000) := by
  have h := checkLog_sound (w := (12979 / 112021)) (n := 12)
    (lo := (116384867 / 500000000)) (hi := (46553947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49521) = 1/(49521 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46553947 / 200000000) (-116384867 / 500000000) (Real.log (49521 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188821221 / 1000000000) ≤ -Real.log (40000 / 48313) ∧
    -Real.log (40000 / 48313) ≤ (94410611 / 500000000) := by
  have h := checkLog_sound (w := (8313 / 88313)) (n := 12)
    (lo := (188821221 / 1000000000)) (hi := (94410611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48313 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48313 / 40000) = 1/(40000 / 48313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188821221 / 1000000000) (94410611 / 500000000) (Real.log (48313 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48313 / 40000) = -Real.log (40000 / 48313) := by
    rw [show ((48313 / 40000) : ℝ) = ((40000 / 48313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (232972951 / 1000000000) ≤ -Real.log (31687 / 40000) ∧
    -Real.log (31687 / 40000) ≤ (29121619 / 125000000) := by
  have h := checkLog_sound (w := (8313 / 71687)) (n := 12)
    (lo := (232972951 / 1000000000)) (hi := (29121619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31687) = 1/(31687 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-29121619 / 125000000) (-232972951 / 1000000000) (Real.log (31687 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118110147 / 200000000) ≤ -Real.log (5000000000 / 9024911047) ∧
    -Real.log (5000000000 / 9024911047) ≤ (36909421 / 62500000) := by
  have h := checkLog_sound (w := (4024911047 / 14024911047)) (n := 12)
    (lo := (118110147 / 200000000)) (hi := (36909421 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9024911047 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9024911047 / 5000000000) = 1/(5000000000 / 9024911047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118110147 / 200000000) (36909421 / 62500000) (Real.log (9024911047 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9024911047 / 5000000000) = -Real.log (5000000000 / 9024911047) := by
    rw [show ((9024911047 / 5000000000) : ℝ) = ((5000000000 / 9024911047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (118203 / 200000) ≤ -Real.log (500000000000 / 902910196913) ∧
    -Real.log (500000000000 / 902910196913) ≤ (591015001 / 1000000000) := by
  have h := checkLog_sound (w := (402910196913 / 1402910196913)) (n := 12)
    (lo := (118203 / 200000)) (hi := (591015001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902910196913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902910196913 / 500000000000) = 1/(500000000000 / 902910196913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (118203 / 200000) (591015001 / 1000000000) (Real.log (902910196913 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (902910196913 / 500000000000) = -Real.log (500000000000 / 902910196913) := by
    rw [show ((902910196913 / 500000000000) : ℝ) = ((500000000000 / 902910196913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421457649 / 1000000000) ≤ -Real.log (62500000000 / 95261353769) ∧
    -Real.log (62500000000 / 95261353769) ≤ (8429153 / 20000000) := by
  have h := checkLog_sound (w := (32761353769 / 157761353769)) (n := 12)
    (lo := (421457649 / 1000000000)) (hi := (8429153 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95261353769 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95261353769 / 62500000000) = 1/(62500000000 / 95261353769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421457649 / 1000000000) (8429153 / 20000000) (Real.log (95261353769 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (95261353769 / 62500000000) = -Real.log (62500000000 / 95261353769) := by
    rw [show ((95261353769 / 62500000000) : ℝ) = ((62500000000 / 95261353769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421794173 / 1000000000) ≤ -Real.log (50000000000 / 76234733487) ∧
    -Real.log (50000000000 / 76234733487) ≤ (210897087 / 500000000) := by
  have h := checkLog_sound (w := (26234733487 / 126234733487)) (n := 12)
    (lo := (421794173 / 1000000000)) (hi := (210897087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76234733487 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76234733487 / 50000000000) = 1/(50000000000 / 76234733487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421794173 / 1000000000) (210897087 / 500000000) (Real.log (76234733487 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76234733487 / 50000000000) = -Real.log (50000000000 / 76234733487) := by
    rw [show ((76234733487 / 50000000000) : ℝ) = ((50000000000 / 76234733487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0469

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0470Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0470
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

theorem reflection_log_1_neg : (36708303 / 200000000) ≤ -Real.log (10240 / 12303) ∧
    -Real.log (10240 / 12303) ≤ (45885379 / 250000000) := by
  have h := checkLog_sound (w := (2063 / 22543)) (n := 12)
    (lo := (36708303 / 200000000)) (hi := (45885379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12303 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12303 / 10240) = 1/(10240 / 12303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (36708303 / 200000000) (45885379 / 250000000) (Real.log (12303 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12303 / 10240) = -Real.log (10240 / 12303) := by
    rw [show ((12303 / 10240) : ℝ) = ((10240 / 12303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56244071 / 250000000) ≤ -Real.log (8177 / 10240) ∧
    -Real.log (8177 / 10240) ≤ (44995257 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 18417)) (n := 12)
    (lo := (56244071 / 250000000)) (hi := (44995257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8177) = 1/(8177 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44995257 / 200000000) (-56244071 / 250000000) (Real.log (8177 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91709793 / 500000000) ≤ -Real.log (20480 / 24603) ∧
    -Real.log (20480 / 24603) ≤ (183419587 / 1000000000) := by
  have h := checkLog_sound (w := (4123 / 45083)) (n := 12)
    (lo := (91709793 / 500000000)) (hi := (183419587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 20480) = 1/(20480 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91709793 / 500000000) (183419587 / 1000000000) (Real.log (24603 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24603 / 20480) = -Real.log (20480 / 24603) := by
    rw [show ((24603 / 20480) : ℝ) = ((20480 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224792859 / 1000000000) ≤ -Real.log (16357 / 20480) ∧
    -Real.log (16357 / 20480) ≤ (11239643 / 50000000) := by
  have h := checkLog_sound (w := (4123 / 36837)) (n := 12)
    (lo := (224792859 / 1000000000)) (hi := (11239643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16357) = 1/(16357 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11239643 / 50000000) (-224792859 / 1000000000) (Real.log (16357 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (84640671 / 250000000) ≤ -Real.log (5120 / 7183) ∧
    -Real.log (5120 / 7183) ≤ (67712537 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 12303)) (n := 12)
    (lo := (84640671 / 250000000)) (hi := (67712537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7183 / 5120) = 1/(5120 / 7183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (84640671 / 250000000) (67712537 / 200000000) (Real.log (7183 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7183 / 5120) = -Real.log (5120 / 7183) := by
    rw [show ((7183 / 5120) : ℝ) = ((5120 / 7183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (128930099 / 250000000) ≤ -Real.log (3057 / 5120) ∧
    -Real.log (3057 / 5120) ≤ (515720397 / 1000000000) := by
  have h := checkLog_sound (w := (2063 / 8177)) (n := 12)
    (lo := (128930099 / 250000000)) (hi := (515720397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3057) = 1/(3057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-515720397 / 1000000000) (-128930099 / 250000000) (Real.log (3057 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67670767 / 200000000) ≤ -Real.log (10240 / 14363) ∧
    -Real.log (10240 / 14363) ≤ (84588459 / 250000000) := by
  have h := checkLog_sound (w := (4123 / 24603)) (n := 12)
    (lo := (67670767 / 200000000)) (hi := (84588459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14363 / 10240) = 1/(10240 / 14363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67670767 / 200000000) (84588459 / 250000000) (Real.log (14363 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14363 / 10240) = -Real.log (10240 / 14363) := by
    rw [show ((14363 / 10240) : ℝ) = ((10240 / 14363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (515229839 / 1000000000) ≤ -Real.log (6117 / 10240) ∧
    -Real.log (6117 / 10240) ≤ (6440373 / 12500000) := by
  have h := checkLog_sound (w := (4123 / 16357)) (n := 12)
    (lo := (515229839 / 1000000000)) (hi := (6440373 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6117) = 1/(6117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6440373 / 12500000) (-515229839 / 1000000000) (Real.log (6117 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252135979 / 1000000000) ≤ -Real.log (1000000 / 1286771) ∧
    -Real.log (1000000 / 1286771) ≤ (12606799 / 50000000) := by
  have h := checkLog_sound (w := (286771 / 2286771)) (n := 12)
    (lo := (252135979 / 1000000000)) (hi := (12606799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286771 / 1000000) = 1/(1000000 / 1286771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252135979 / 1000000000) (12606799 / 50000000) (Real.log (1286771 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286771 / 1000000) = -Real.log (1000000 / 1286771) := by
    rw [show ((1286771 / 1000000) : ℝ) = ((1000000 / 1286771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84488183 / 250000000) ≤ -Real.log (713229 / 1000000) ∧
    -Real.log (713229 / 1000000) ≤ (337952733 / 1000000000) := by
  have h := checkLog_sound (w := (286771 / 1713229)) (n := 12)
    (lo := (84488183 / 250000000)) (hi := (337952733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713229) = 1/(713229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337952733 / 1000000000) (-84488183 / 250000000) (Real.log (713229 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31537687 / 125000000) ≤ -Real.log (125000 / 160873) ∧
    -Real.log (125000 / 160873) ≤ (252301497 / 1000000000) := by
  have h := checkLog_sound (w := (35873 / 285873)) (n := 12)
    (lo := (31537687 / 125000000)) (hi := (252301497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160873 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160873 / 125000) = 1/(125000 / 160873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31537687 / 125000000) (252301497 / 1000000000) (Real.log (160873 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (160873 / 125000) = -Real.log (125000 / 160873) := by
    rw [show ((160873 / 125000) : ℝ) = ((125000 / 160873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (169125709 / 500000000) ≤ -Real.log (89127 / 125000) ∧
    -Real.log (89127 / 125000) ≤ (338251419 / 1000000000) := by
  have h := checkLog_sound (w := (35873 / 214127)) (n := 12)
    (lo := (169125709 / 500000000)) (hi := (338251419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89127) = 1/(89127 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-338251419 / 1000000000) (-169125709 / 500000000) (Real.log (89127 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188554591 / 1000000000) ≤ -Real.log (1000000 / 1207503) ∧
    -Real.log (1000000 / 1207503) ≤ (5892331 / 31250000) := by
  have h := checkLog_sound (w := (207503 / 2207503)) (n := 12)
    (lo := (188554591 / 1000000000)) (hi := (5892331 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207503 / 1000000) = 1/(1000000 / 1207503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188554591 / 1000000000) (5892331 / 31250000) (Real.log (1207503 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207503 / 1000000) = -Real.log (1000000 / 1207503) := by
    rw [show ((1207503 / 1000000) : ℝ) = ((1000000 / 1207503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (116283279 / 500000000) ≤ -Real.log (792497 / 1000000) ∧
    -Real.log (792497 / 1000000) ≤ (232566559 / 1000000000) := by
  have h := checkLog_sound (w := (207503 / 1792497)) (n := 12)
    (lo := (116283279 / 500000000)) (hi := (232566559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792497) = 1/(792497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-232566559 / 1000000000) (-116283279 / 500000000) (Real.log (792497 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188688743 / 1000000000) ≤ -Real.log (200000 / 241533) ∧
    -Real.log (200000 / 241533) ≤ (23586093 / 125000000) := by
  have h := checkLog_sound (w := (41533 / 441533)) (n := 12)
    (lo := (188688743 / 1000000000)) (hi := (23586093 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241533 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241533 / 200000) = 1/(200000 / 241533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188688743 / 1000000000) (23586093 / 125000000) (Real.log (241533 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (241533 / 200000) = -Real.log (200000 / 241533) := by
    rw [show ((241533 / 200000) : ℝ) = ((200000 / 241533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58192749 / 250000000) ≤ -Real.log (158467 / 200000) ∧
    -Real.log (158467 / 200000) ≤ (232770997 / 1000000000) := by
  have h := checkLog_sound (w := (41533 / 358467)) (n := 12)
    (lo := (58192749 / 250000000)) (hi := (232770997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158467) = 1/(158467 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-232770997 / 1000000000) (-58192749 / 250000000) (Real.log (158467 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (590088711 / 1000000000) ≤ -Real.log (500000000000 / 902074228613) ∧
    -Real.log (500000000000 / 902074228613) ≤ (73761089 / 125000000) := by
  have h := checkLog_sound (w := (402074228613 / 1402074228613)) (n := 12)
    (lo := (590088711 / 1000000000)) (hi := (73761089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902074228613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902074228613 / 500000000000) = 1/(500000000000 / 902074228613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (590088711 / 1000000000) (73761089 / 125000000) (Real.log (902074228613 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (902074228613 / 500000000000) = -Real.log (500000000000 / 902074228613) := by
    rw [show ((902074228613 / 500000000000) : ℝ) = ((500000000000 / 902074228613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (295276457 / 500000000) ≤ -Real.log (100000000000 / 180498614337) ∧
    -Real.log (100000000000 / 180498614337) ≤ (118110583 / 200000000) := by
  have h := checkLog_sound (w := (80498614337 / 280498614337)) (n := 12)
    (lo := (295276457 / 500000000)) (hi := (118110583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180498614337 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180498614337 / 100000000000) = 1/(100000000000 / 180498614337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (295276457 / 500000000) (118110583 / 200000000) (Real.log (180498614337 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (180498614337 / 100000000000) = -Real.log (100000000000 / 180498614337) := by
    rw [show ((180498614337 / 100000000000) : ℝ) = ((100000000000 / 180498614337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421121149 / 1000000000) ≤ -Real.log (500000000000 / 761834429657) ∧
    -Real.log (500000000000 / 761834429657) ≤ (8422423 / 20000000) := by
  have h := checkLog_sound (w := (261834429657 / 1261834429657)) (n := 12)
    (lo := (421121149 / 1000000000)) (hi := (8422423 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761834429657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761834429657 / 500000000000) = 1/(500000000000 / 761834429657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421121149 / 1000000000) (8422423 / 20000000) (Real.log (761834429657 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761834429657 / 500000000000) = -Real.log (500000000000 / 761834429657) := by
    rw [show ((761834429657 / 500000000000) : ℝ) = ((500000000000 / 761834429657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421459739 / 1000000000) ≤ -Real.log (500000000000 / 762092423029) ∧
    -Real.log (500000000000 / 762092423029) ≤ (21072987 / 50000000) := by
  have h := checkLog_sound (w := (262092423029 / 1262092423029)) (n := 12)
    (lo := (421459739 / 1000000000)) (hi := (21072987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762092423029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762092423029 / 500000000000) = 1/(500000000000 / 762092423029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421459739 / 1000000000) (21072987 / 50000000) (Real.log (762092423029 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (762092423029 / 500000000000) = -Real.log (500000000000 / 762092423029) := by
    rw [show ((762092423029 / 500000000000) : ℝ) = ((500000000000 / 762092423029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0470

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0471Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0471
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

theorem reflection_log_1_neg : (91709793 / 500000000) ≤ -Real.log (20480 / 24603) ∧
    -Real.log (20480 / 24603) ≤ (183419587 / 1000000000) := by
  have h := checkLog_sound (w := (4123 / 45083)) (n := 12)
    (lo := (91709793 / 500000000)) (hi := (183419587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 20480) = 1/(20480 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91709793 / 500000000) (183419587 / 1000000000) (Real.log (24603 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24603 / 20480) = -Real.log (20480 / 24603) := by
    rw [show ((24603 / 20480) : ℝ) = ((20480 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224792859 / 1000000000) ≤ -Real.log (16357 / 20480) ∧
    -Real.log (16357 / 20480) ≤ (11239643 / 50000000) := by
  have h := checkLog_sound (w := (4123 / 36837)) (n := 12)
    (lo := (224792859 / 1000000000)) (hi := (11239643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16357) = 1/(16357 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11239643 / 50000000) (-224792859 / 1000000000) (Real.log (16357 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91648821 / 500000000) ≤ -Real.log (512 / 615) ∧
    -Real.log (512 / 615) ≤ (183297643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1127)) (n := 12)
    (lo := (91648821 / 500000000)) (hi := (183297643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615 / 512) = 1/(512 / 615) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91648821 / 500000000) (183297643 / 1000000000) (Real.log (615 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (615 / 512) = -Real.log (512 / 615) := by
    rw [show ((615 / 512) : ℝ) = ((512 / 615) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56152367 / 250000000) ≤ -Real.log (409 / 512) ∧
    -Real.log (409 / 512) ≤ (224609469 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 921)) (n := 12)
    (lo := (56152367 / 250000000)) (hi := (224609469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 409) = 1/(409 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224609469 / 1000000000) (-56152367 / 250000000) (Real.log (409 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67670767 / 200000000) ≤ -Real.log (10240 / 14363) ∧
    -Real.log (10240 / 14363) ≤ (84588459 / 250000000) := by
  have h := checkLog_sound (w := (4123 / 24603)) (n := 12)
    (lo := (67670767 / 200000000)) (hi := (84588459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14363 / 10240) = 1/(10240 / 14363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (67670767 / 200000000) (84588459 / 250000000) (Real.log (14363 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14363 / 10240) = -Real.log (10240 / 14363) := by
    rw [show ((14363 / 10240) : ℝ) = ((10240 / 14363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (515229839 / 1000000000) ≤ -Real.log (6117 / 10240) ∧
    -Real.log (6117 / 10240) ≤ (6440373 / 12500000) := by
  have h := checkLog_sound (w := (4123 / 16357)) (n := 12)
    (lo := (515229839 / 1000000000)) (hi := (6440373 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6117) = 1/(6117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6440373 / 12500000) (-515229839 / 1000000000) (Real.log (6117 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21134059 / 62500000) ≤ -Real.log (256 / 359) ∧
    -Real.log (256 / 359) ≤ (67628989 / 200000000) := by
  have h := checkLog_sound (w := (103 / 615)) (n := 12)
    (lo := (21134059 / 62500000)) (hi := (67628989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359 / 256) = 1/(256 / 359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21134059 / 62500000) (67628989 / 200000000) (Real.log (359 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (359 / 256) = -Real.log (256 / 359) := by
    rw [show ((359 / 256) : ℝ) = ((256 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (514739523 / 1000000000) ≤ -Real.log (153 / 256) ∧
    -Real.log (153 / 256) ≤ (128684881 / 250000000) := by
  have h := checkLog_sound (w := (103 / 409)) (n := 12)
    (lo := (514739523 / 1000000000)) (hi := (128684881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 153) = 1/(153 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128684881 / 250000000) (-514739523 / 1000000000) (Real.log (153 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62992803 / 250000000) ≤ -Real.log (1000000 / 1286559) ∧
    -Real.log (1000000 / 1286559) ≤ (251971213 / 1000000000) := by
  have h := checkLog_sound (w := (286559 / 2286559)) (n := 12)
    (lo := (62992803 / 250000000)) (hi := (251971213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286559 / 1000000) = 1/(1000000 / 1286559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62992803 / 250000000) (251971213 / 1000000000) (Real.log (1286559 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286559 / 1000000) = -Real.log (1000000 / 1286559) := by
    rw [show ((1286559 / 1000000) : ℝ) = ((1000000 / 1286559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21103471 / 62500000) ≤ -Real.log (713441 / 1000000) ∧
    -Real.log (713441 / 1000000) ≤ (337655537 / 1000000000) := by
  have h := checkLog_sound (w := (286559 / 1713441)) (n := 12)
    (lo := (21103471 / 62500000)) (hi := (337655537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713441) = 1/(713441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337655537 / 1000000000) (-21103471 / 62500000) (Real.log (713441 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63034189 / 250000000) ≤ -Real.log (250000 / 321693) ∧
    -Real.log (250000 / 321693) ≤ (252136757 / 1000000000) := by
  have h := checkLog_sound (w := (71693 / 571693)) (n := 12)
    (lo := (63034189 / 250000000)) (hi := (252136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321693 / 250000) = 1/(250000 / 321693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63034189 / 250000000) (252136757 / 1000000000) (Real.log (321693 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (321693 / 250000) = -Real.log (250000 / 321693) := by
    rw [show ((321693 / 250000) : ℝ) = ((250000 / 321693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (168977067 / 500000000) ≤ -Real.log (178307 / 250000) ∧
    -Real.log (178307 / 250000) ≤ (67590827 / 200000000) := by
  have h := checkLog_sound (w := (71693 / 428307)) (n := 12)
    (lo := (168977067 / 500000000)) (hi := (67590827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178307) = 1/(178307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67590827 / 200000000) (-168977067 / 500000000) (Real.log (178307 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188422077 / 1000000000) ≤ -Real.log (1000000 / 1207343) ∧
    -Real.log (1000000 / 1207343) ≤ (94211039 / 500000000) := by
  have h := checkLog_sound (w := (207343 / 2207343)) (n := 12)
    (lo := (188422077 / 1000000000)) (hi := (94211039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207343 / 1000000) = 1/(1000000 / 1207343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188422077 / 1000000000) (94211039 / 500000000) (Real.log (1207343 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207343 / 1000000) = -Real.log (1000000 / 1207343) := by
    rw [show ((1207343 / 1000000) : ℝ) = ((1000000 / 1207343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (46472937 / 200000000) ≤ -Real.log (792657 / 1000000) ∧
    -Real.log (792657 / 1000000) ≤ (116182343 / 500000000) := by
  have h := checkLog_sound (w := (207343 / 1792657)) (n := 12)
    (lo := (46472937 / 200000000)) (hi := (116182343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792657) = 1/(792657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116182343 / 500000000) (-46472937 / 200000000) (Real.log (792657 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188555419 / 1000000000) ≤ -Real.log (62500 / 75469) ∧
    -Real.log (62500 / 75469) ≤ (9427771 / 50000000) := by
  have h := checkLog_sound (w := (12969 / 137969)) (n := 12)
    (lo := (188555419 / 1000000000)) (hi := (9427771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75469 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75469 / 62500) = 1/(62500 / 75469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188555419 / 1000000000) (9427771 / 50000000) (Real.log (75469 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75469 / 62500) = -Real.log (62500 / 75469) := by
    rw [show ((75469 / 62500) : ℝ) = ((62500 / 75469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11628391 / 50000000) ≤ -Real.log (49531 / 62500) ∧
    -Real.log (49531 / 62500) ≤ (232567821 / 1000000000) := by
  have h := checkLog_sound (w := (12969 / 112031)) (n := 12)
    (lo := (11628391 / 50000000)) (hi := (232567821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49531) = 1/(49531 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-232567821 / 1000000000) (-11628391 / 50000000) (Real.log (49531 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (147406687 / 250000000) ≤ -Real.log (250000000000 / 450828800139) ∧
    -Real.log (250000000000 / 450828800139) ≤ (589626749 / 1000000000) := by
  have h := checkLog_sound (w := (200828800139 / 700828800139)) (n := 12)
    (lo := (147406687 / 250000000)) (hi := (589626749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450828800139 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450828800139 / 250000000000) = 1/(250000000000 / 450828800139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (147406687 / 250000000) (589626749 / 1000000000) (Real.log (450828800139 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (450828800139 / 250000000000) = -Real.log (250000000000 / 450828800139) := by
    rw [show ((450828800139 / 250000000000) : ℝ) = ((250000000000 / 450828800139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59009089 / 100000000) ≤ -Real.log (500000000000 / 902076194429) ∧
    -Real.log (500000000000 / 902076194429) ≤ (590090891 / 1000000000) := by
  have h := checkLog_sound (w := (402076194429 / 1402076194429)) (n := 12)
    (lo := (59009089 / 100000000)) (hi := (590090891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902076194429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902076194429 / 500000000000) = 1/(500000000000 / 902076194429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59009089 / 100000000) (590090891 / 1000000000) (Real.log (902076194429 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (902076194429 / 500000000000) = -Real.log (500000000000 / 902076194429) := by
    rw [show ((902076194429 / 500000000000) : ℝ) = ((500000000000 / 902076194429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (210393381 / 500000000) ≤ -Real.log (500000000000 / 761579724899) ∧
    -Real.log (500000000000 / 761579724899) ≤ (420786763 / 1000000000) := by
  have h := checkLog_sound (w := (261579724899 / 1261579724899)) (n := 12)
    (lo := (210393381 / 500000000)) (hi := (420786763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761579724899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761579724899 / 500000000000) = 1/(500000000000 / 761579724899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (210393381 / 500000000) (420786763 / 1000000000) (Real.log (761579724899 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761579724899 / 500000000000) = -Real.log (500000000000 / 761579724899) := by
    rw [show ((761579724899 / 500000000000) : ℝ) = ((500000000000 / 761579724899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421123239 / 1000000000) ≤ -Real.log (250000000000 / 380918010943) ∧
    -Real.log (250000000000 / 380918010943) ≤ (10528081 / 25000000) := by
  have h := checkLog_sound (w := (130918010943 / 630918010943)) (n := 12)
    (lo := (421123239 / 1000000000)) (hi := (10528081 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380918010943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380918010943 / 250000000000) = 1/(250000000000 / 380918010943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421123239 / 1000000000) (10528081 / 25000000) (Real.log (380918010943 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (380918010943 / 250000000000) = -Real.log (250000000000 / 380918010943) := by
    rw [show ((380918010943 / 250000000000) : ℝ) = ((250000000000 / 380918010943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0471

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0472Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0472
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

theorem reflection_log_1_neg : (91648821 / 500000000) ≤ -Real.log (512 / 615) ∧
    -Real.log (512 / 615) ≤ (183297643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1127)) (n := 12)
    (lo := (91648821 / 500000000)) (hi := (183297643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615 / 512) = 1/(512 / 615) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91648821 / 500000000) (183297643 / 1000000000) (Real.log (615 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (615 / 512) = -Real.log (512 / 615) := by
    rw [show ((615 / 512) : ℝ) = ((512 / 615) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56152367 / 250000000) ≤ -Real.log (409 / 512) ∧
    -Real.log (409 / 512) ≤ (224609469 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 921)) (n := 12)
    (lo := (56152367 / 250000000)) (hi := (224609469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 409) = 1/(409 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-224609469 / 1000000000) (-56152367 / 250000000) (Real.log (409 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45793921 / 250000000) ≤ -Real.log (20480 / 24597) ∧
    -Real.log (20480 / 24597) ≤ (36635137 / 200000000) := by
  have h := checkLog_sound (w := (4117 / 45077)) (n := 12)
    (lo := (45793921 / 250000000)) (hi := (36635137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24597 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24597 / 20480) = 1/(20480 / 24597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45793921 / 250000000) (36635137 / 200000000) (Real.log (24597 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24597 / 20480) = -Real.log (20480 / 24597) := by
    rw [show ((24597 / 20480) : ℝ) = ((20480 / 24597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224426111 / 1000000000) ≤ -Real.log (16363 / 20480) ∧
    -Real.log (16363 / 20480) ≤ (1753329 / 7812500) := by
  have h := checkLog_sound (w := (4117 / 36843)) (n := 12)
    (lo := (224426111 / 1000000000)) (hi := (1753329 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16363) = 1/(16363 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1753329 / 7812500) (-224426111 / 1000000000) (Real.log (16363 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21134059 / 62500000) ≤ -Real.log (256 / 359) ∧
    -Real.log (256 / 359) ≤ (67628989 / 200000000) := by
  have h := checkLog_sound (w := (103 / 615)) (n := 12)
    (lo := (21134059 / 62500000)) (hi := (67628989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359 / 256) = 1/(256 / 359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21134059 / 62500000) (67628989 / 200000000) (Real.log (359 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (359 / 256) = -Real.log (256 / 359) := by
    rw [show ((359 / 256) : ℝ) = ((256 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (514739523 / 1000000000) ≤ -Real.log (153 / 256) ∧
    -Real.log (153 / 256) ≤ (128684881 / 250000000) := by
  have h := checkLog_sound (w := (103 / 409)) (n := 12)
    (lo := (514739523 / 1000000000)) (hi := (128684881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 153) = 1/(153 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128684881 / 250000000) (-514739523 / 1000000000) (Real.log (153 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42242001 / 125000000) ≤ -Real.log (10240 / 14357) ∧
    -Real.log (10240 / 14357) ≤ (337936009 / 1000000000) := by
  have h := checkLog_sound (w := (4117 / 24597)) (n := 12)
    (lo := (42242001 / 125000000)) (hi := (337936009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14357 / 10240) = 1/(10240 / 14357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42242001 / 125000000) (337936009 / 1000000000) (Real.log (14357 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14357 / 10240) = -Real.log (10240 / 14357) := by
    rw [show ((14357 / 10240) : ℝ) = ((10240 / 14357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (514249447 / 1000000000) ≤ -Real.log (6123 / 10240) ∧
    -Real.log (6123 / 10240) ≤ (64281181 / 125000000) := by
  have h := checkLog_sound (w := (4117 / 16363)) (n := 12)
    (lo := (514249447 / 1000000000)) (hi := (64281181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6123) = 1/(6123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-64281181 / 125000000) (-514249447 / 1000000000) (Real.log (6123 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50361439 / 200000000) ≤ -Real.log (250000 / 321587) ∧
    -Real.log (250000 / 321587) ≤ (62951799 / 250000000) := by
  have h := checkLog_sound (w := (71587 / 571587)) (n := 12)
    (lo := (50361439 / 200000000)) (hi := (62951799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321587 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321587 / 250000) = 1/(250000 / 321587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50361439 / 200000000) (62951799 / 250000000) (Real.log (321587 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321587 / 250000) = -Real.log (250000 / 321587) := by
    rw [show ((321587 / 250000) : ℝ) = ((250000 / 321587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (33735983 / 100000000) ≤ -Real.log (178413 / 250000) ∧
    -Real.log (178413 / 250000) ≤ (337359831 / 1000000000) := by
  have h := checkLog_sound (w := (71587 / 428413)) (n := 12)
    (lo := (33735983 / 100000000)) (hi := (337359831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178413) = 1/(178413 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337359831 / 1000000000) (-33735983 / 100000000) (Real.log (178413 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251972767 / 1000000000) ≤ -Real.log (1000000 / 1286561) ∧
    -Real.log (1000000 / 1286561) ≤ (7874149 / 31250000) := by
  have h := checkLog_sound (w := (286561 / 2286561)) (n := 12)
    (lo := (251972767 / 1000000000)) (hi := (7874149 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286561 / 1000000) = 1/(1000000 / 1286561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251972767 / 1000000000) (7874149 / 31250000) (Real.log (1286561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286561 / 1000000) = -Real.log (1000000 / 1286561) := by
    rw [show ((1286561 / 1000000) : ℝ) = ((1000000 / 1286561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337658339 / 1000000000) ≤ -Real.log (713439 / 1000000) ∧
    -Real.log (713439 / 1000000) ≤ (16882917 / 50000000) := by
  have h := checkLog_sound (w := (286561 / 1713439)) (n := 12)
    (lo := (337658339 / 1000000000)) (hi := (16882917 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713439) = 1/(713439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16882917 / 50000000) (-337658339 / 1000000000) (Real.log (713439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94144773 / 500000000) ≤ -Real.log (1000000 / 1207183) ∧
    -Real.log (1000000 / 1207183) ≤ (188289547 / 1000000000) := by
  have h := checkLog_sound (w := (207183 / 2207183)) (n := 12)
    (lo := (94144773 / 500000000)) (hi := (188289547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207183 / 1000000) = 1/(1000000 / 1207183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94144773 / 500000000) (188289547 / 1000000000) (Real.log (1207183 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207183 / 1000000) = -Real.log (1000000 / 1207183) := by
    rw [show ((1207183 / 1000000) : ℝ) = ((1000000 / 1207183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (232162853 / 1000000000) ≤ -Real.log (792817 / 1000000) ∧
    -Real.log (792817 / 1000000) ≤ (116081427 / 500000000) := by
  have h := checkLog_sound (w := (207183 / 1792817)) (n := 12)
    (lo := (232162853 / 1000000000)) (hi := (116081427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792817) = 1/(792817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116081427 / 500000000) (-232162853 / 1000000000) (Real.log (792817 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (37684581 / 200000000) ≤ -Real.log (62500 / 75459) ∧
    -Real.log (62500 / 75459) ≤ (94211453 / 500000000) := by
  have h := checkLog_sound (w := (12959 / 137959)) (n := 12)
    (lo := (37684581 / 200000000)) (hi := (94211453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75459 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75459 / 62500) = 1/(62500 / 75459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37684581 / 200000000) (94211453 / 500000000) (Real.log (75459 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75459 / 62500) = -Real.log (62500 / 75459) := by
    rw [show ((75459 / 62500) : ℝ) = ((62500 / 75459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (232365947 / 1000000000) ≤ -Real.log (49541 / 62500) ∧
    -Real.log (49541 / 62500) ≤ (58091487 / 250000000) := by
  have h := checkLog_sound (w := (12959 / 112041)) (n := 12)
    (lo := (232365947 / 1000000000)) (hi := (58091487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49541) = 1/(49541 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58091487 / 250000000) (-232365947 / 1000000000) (Real.log (49541 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (294583513 / 500000000) ≤ -Real.log (500000000000 / 901243182951) ∧
    -Real.log (500000000000 / 901243182951) ≤ (589167027 / 1000000000) := by
  have h := checkLog_sound (w := (401243182951 / 1401243182951)) (n := 12)
    (lo := (294583513 / 500000000)) (hi := (589167027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901243182951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(901243182951 / 500000000000) = 1/(500000000000 / 901243182951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (294583513 / 500000000) (589167027 / 1000000000) (Real.log (901243182951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (901243182951 / 500000000000) = -Real.log (500000000000 / 901243182951) := by
    rw [show ((901243182951 / 500000000000) : ℝ) = ((500000000000 / 901243182951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (294815553 / 500000000) ≤ -Real.log (250000000000 / 450830764789) ∧
    -Real.log (250000000000 / 450830764789) ≤ (589631107 / 1000000000) := by
  have h := checkLog_sound (w := (200830764789 / 700830764789)) (n := 12)
    (lo := (294815553 / 500000000)) (hi := (589631107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450830764789 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450830764789 / 250000000000) = 1/(250000000000 / 450830764789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (294815553 / 500000000) (589631107 / 1000000000) (Real.log (450830764789 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450830764789 / 250000000000) = -Real.log (250000000000 / 450830764789) := by
    rw [show ((450830764789 / 250000000000) : ℝ) = ((250000000000 / 450830764789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (420452399 / 1000000000) ≤ -Real.log (500000000000 / 761325122947) ∧
    -Real.log (500000000000 / 761325122947) ≤ (1051131 / 2500000) := by
  have h := checkLog_sound (w := (261325122947 / 1261325122947)) (n := 12)
    (lo := (420452399 / 1000000000)) (hi := (1051131 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761325122947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761325122947 / 500000000000) = 1/(500000000000 / 761325122947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (420452399 / 1000000000) (1051131 / 2500000) (Real.log (761325122947 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761325122947 / 500000000000) = -Real.log (500000000000 / 761325122947) := by
    rw [show ((761325122947 / 500000000000) : ℝ) = ((500000000000 / 761325122947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (105197213 / 250000000) ≤ -Real.log (250000000000 / 380790658243) ∧
    -Real.log (250000000000 / 380790658243) ≤ (420788853 / 1000000000) := by
  have h := checkLog_sound (w := (130790658243 / 630790658243)) (n := 12)
    (lo := (105197213 / 250000000)) (hi := (420788853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380790658243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380790658243 / 250000000000) = 1/(250000000000 / 380790658243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (105197213 / 250000000) (420788853 / 1000000000) (Real.log (380790658243 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (380790658243 / 250000000000) = -Real.log (250000000000 / 380790658243) := by
    rw [show ((380790658243 / 250000000000) : ℝ) = ((250000000000 / 380790658243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0472

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0473Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0473
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

theorem reflection_log_1_neg : (45793921 / 250000000) ≤ -Real.log (20480 / 24597) ∧
    -Real.log (20480 / 24597) ≤ (36635137 / 200000000) := by
  have h := checkLog_sound (w := (4117 / 45077)) (n := 12)
    (lo := (45793921 / 250000000)) (hi := (36635137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24597 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24597 / 20480) = 1/(20480 / 24597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (45793921 / 250000000) (36635137 / 200000000) (Real.log (24597 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24597 / 20480) = -Real.log (20480 / 24597) := by
    rw [show ((24597 / 20480) : ℝ) = ((20480 / 24597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224426111 / 1000000000) ≤ -Real.log (16363 / 20480) ∧
    -Real.log (16363 / 20480) ≤ (1753329 / 7812500) := by
  have h := checkLog_sound (w := (4117 / 36843)) (n := 12)
    (lo := (224426111 / 1000000000)) (hi := (1753329 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16363) = 1/(16363 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1753329 / 7812500) (-224426111 / 1000000000) (Real.log (16363 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18305371 / 100000000) ≤ -Real.log (10240 / 12297) ∧
    -Real.log (10240 / 12297) ≤ (183053711 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 22537)) (n := 12)
    (lo := (18305371 / 100000000)) (hi := (183053711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 10240) = 1/(10240 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18305371 / 100000000) (183053711 / 1000000000) (Real.log (12297 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12297 / 10240) = -Real.log (10240 / 12297) := by
    rw [show ((12297 / 10240) : ℝ) = ((10240 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56060697 / 250000000) ≤ -Real.log (8183 / 10240) ∧
    -Real.log (8183 / 10240) ≤ (224242789 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 18423)) (n := 12)
    (lo := (56060697 / 250000000)) (hi := (224242789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8183) = 1/(8183 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224242789 / 1000000000) (-56060697 / 250000000) (Real.log (8183 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42242001 / 125000000) ≤ -Real.log (10240 / 14357) ∧
    -Real.log (10240 / 14357) ≤ (337936009 / 1000000000) := by
  have h := checkLog_sound (w := (4117 / 24597)) (n := 12)
    (lo := (42242001 / 125000000)) (hi := (337936009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14357 / 10240) = 1/(10240 / 14357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42242001 / 125000000) (337936009 / 1000000000) (Real.log (14357 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14357 / 10240) = -Real.log (10240 / 14357) := by
    rw [show ((14357 / 10240) : ℝ) = ((10240 / 14357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (514249447 / 1000000000) ≤ -Real.log (6123 / 10240) ∧
    -Real.log (6123 / 10240) ≤ (64281181 / 125000000) := by
  have h := checkLog_sound (w := (4117 / 16363)) (n := 12)
    (lo := (514249447 / 1000000000)) (hi := (64281181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6123) = 1/(6123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-64281181 / 125000000) (-514249447 / 1000000000) (Real.log (6123 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (337727029 / 1000000000) ≤ -Real.log (5120 / 7177) ∧
    -Real.log (5120 / 7177) ≤ (33772703 / 100000000) := by
  have h := checkLog_sound (w := (2057 / 12297)) (n := 12)
    (lo := (337727029 / 1000000000)) (hi := (33772703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7177 / 5120) = 1/(5120 / 7177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (337727029 / 1000000000) (33772703 / 100000000) (Real.log (7177 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7177 / 5120) = -Real.log (5120 / 7177) := by
    rw [show ((7177 / 5120) : ℝ) = ((5120 / 7177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (513759611 / 1000000000) ≤ -Real.log (3063 / 5120) ∧
    -Real.log (3063 / 5120) ≤ (128439903 / 250000000) := by
  have h := checkLog_sound (w := (2057 / 8183)) (n := 12)
    (lo := (513759611 / 1000000000)) (hi := (128439903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3063) = 1/(3063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128439903 / 250000000) (-513759611 / 1000000000) (Real.log (3063 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125821187 / 500000000) ≤ -Real.log (125000 / 160767) ∧
    -Real.log (125000 / 160767) ≤ (2013139 / 8000000) := by
  have h := checkLog_sound (w := (35767 / 285767)) (n := 12)
    (lo := (125821187 / 500000000)) (hi := (2013139 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160767 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160767 / 125000) = 1/(125000 / 160767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125821187 / 500000000) (2013139 / 8000000) (Real.log (160767 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160767 / 125000) = -Real.log (125000 / 160767) := by
    rw [show ((160767 / 125000) : ℝ) = ((125000 / 160767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (33706281 / 100000000) ≤ -Real.log (89233 / 125000) ∧
    -Real.log (89233 / 125000) ≤ (337062811 / 1000000000) := by
  have h := checkLog_sound (w := (35767 / 214233)) (n := 12)
    (lo := (33706281 / 100000000)) (hi := (337062811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89233) = 1/(89233 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337062811 / 1000000000) (-33706281 / 100000000) (Real.log (89233 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251807973 / 1000000000) ≤ -Real.log (1000000 / 1286349) ∧
    -Real.log (1000000 / 1286349) ≤ (125903987 / 500000000) := by
  have h := checkLog_sound (w := (286349 / 2286349)) (n := 12)
    (lo := (251807973 / 1000000000)) (hi := (125903987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286349 / 1000000) = 1/(1000000 / 1286349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251807973 / 1000000000) (125903987 / 500000000) (Real.log (1286349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286349 / 1000000) = -Real.log (1000000 / 1286349) := by
    rw [show ((1286349 / 1000000) : ℝ) = ((1000000 / 1286349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337361231 / 1000000000) ≤ -Real.log (713651 / 1000000) ∧
    -Real.log (713651 / 1000000) ≤ (21085077 / 62500000) := by
  have h := checkLog_sound (w := (286349 / 1713651)) (n := 12)
    (lo := (337361231 / 1000000000)) (hi := (21085077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713651) = 1/(713651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21085077 / 62500000) (-337361231 / 1000000000) (Real.log (713651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23519521 / 125000000) ≤ -Real.log (500000 / 603511) ∧
    -Real.log (500000 / 603511) ≤ (188156169 / 1000000000) := by
  have h := checkLog_sound (w := (103511 / 1103511)) (n := 12)
    (lo := (23519521 / 125000000)) (hi := (188156169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603511 / 500000) = 1/(500000 / 603511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23519521 / 125000000) (188156169 / 1000000000) (Real.log (603511 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (603511 / 500000) = -Real.log (500000 / 603511) := by
    rw [show ((603511 / 500000) : ℝ) = ((500000 / 603511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1159799 / 5000000) ≤ -Real.log (396489 / 500000) ∧
    -Real.log (396489 / 500000) ≤ (231959801 / 1000000000) := by
  have h := checkLog_sound (w := (103511 / 896489)) (n := 12)
    (lo := (1159799 / 5000000)) (hi := (231959801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396489) = 1/(396489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231959801 / 1000000000) (-1159799 / 5000000) (Real.log (396489 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94145187 / 500000000) ≤ -Real.log (62500 / 75449) ∧
    -Real.log (62500 / 75449) ≤ (1506323 / 8000000) := by
  have h := checkLog_sound (w := (12949 / 137949)) (n := 12)
    (lo := (94145187 / 500000000)) (hi := (1506323 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75449 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75449 / 62500) = 1/(62500 / 75449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94145187 / 500000000) (1506323 / 8000000) (Real.log (75449 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75449 / 62500) = -Real.log (62500 / 75449) := by
    rw [show ((75449 / 62500) : ℝ) = ((62500 / 75449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (116082057 / 500000000) ≤ -Real.log (49551 / 62500) ∧
    -Real.log (49551 / 62500) ≤ (46432823 / 200000000) := by
  have h := checkLog_sound (w := (12949 / 112051)) (n := 12)
    (lo := (116082057 / 500000000)) (hi := (46432823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49551) = 1/(49551 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46432823 / 200000000) (-116082057 / 500000000) (Real.log (49551 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117741037 / 200000000) ≤ -Real.log (500000000000 / 900827048289) ∧
    -Real.log (500000000000 / 900827048289) ≤ (294352593 / 500000000) := by
  have h := checkLog_sound (w := (400827048289 / 1400827048289)) (n := 12)
    (lo := (117741037 / 200000000)) (hi := (294352593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900827048289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900827048289 / 500000000000) = 1/(500000000000 / 900827048289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117741037 / 200000000) (294352593 / 500000000) (Real.log (900827048289 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (900827048289 / 500000000000) = -Real.log (500000000000 / 900827048289) := by
    rw [show ((900827048289 / 500000000000) : ℝ) = ((500000000000 / 900827048289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (147292301 / 250000000) ≤ -Real.log (250000000000 / 450622573219) ∧
    -Real.log (250000000000 / 450622573219) ≤ (117833841 / 200000000) := by
  have h := checkLog_sound (w := (200622573219 / 700622573219)) (n := 12)
    (lo := (147292301 / 250000000)) (hi := (117833841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450622573219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450622573219 / 250000000000) = 1/(250000000000 / 450622573219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (147292301 / 250000000) (117833841 / 200000000) (Real.log (450622573219 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450622573219 / 250000000000) = -Real.log (250000000000 / 450622573219) := by
    rw [show ((450622573219 / 250000000000) : ℝ) = ((250000000000 / 450622573219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (420115969 / 1000000000) ≤ -Real.log (500000000000 / 761069033441) ∧
    -Real.log (500000000000 / 761069033441) ≤ (42011597 / 100000000) := by
  have h := checkLog_sound (w := (261069033441 / 1261069033441)) (n := 12)
    (lo := (420115969 / 1000000000)) (hi := (42011597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761069033441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761069033441 / 500000000000) = 1/(500000000000 / 761069033441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (420115969 / 1000000000) (42011597 / 100000000) (Real.log (761069033441 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761069033441 / 500000000000) = -Real.log (500000000000 / 761069033441) := by
    rw [show ((761069033441 / 500000000000) : ℝ) = ((500000000000 / 761069033441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (420454489 / 1000000000) ≤ -Real.log (500000000000 / 761326713891) ∧
    -Real.log (500000000000 / 761326713891) ≤ (42045449 / 100000000) := by
  have h := checkLog_sound (w := (261326713891 / 1261326713891)) (n := 12)
    (lo := (420454489 / 1000000000)) (hi := (42045449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761326713891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761326713891 / 500000000000) = 1/(500000000000 / 761326713891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (420454489 / 1000000000) (42045449 / 100000000) (Real.log (761326713891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (761326713891 / 500000000000) = -Real.log (500000000000 / 761326713891) := by
    rw [show ((761326713891 / 500000000000) : ℝ) = ((500000000000 / 761326713891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0473

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0474Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0474
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

theorem reflection_log_1_neg : (18305371 / 100000000) ≤ -Real.log (10240 / 12297) ∧
    -Real.log (10240 / 12297) ≤ (183053711 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 22537)) (n := 12)
    (lo := (18305371 / 100000000)) (hi := (183053711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 10240) = 1/(10240 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18305371 / 100000000) (183053711 / 1000000000) (Real.log (12297 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12297 / 10240) = -Real.log (10240 / 12297) := by
    rw [show ((12297 / 10240) : ℝ) = ((10240 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56060697 / 250000000) ≤ -Real.log (8183 / 10240) ∧
    -Real.log (8183 / 10240) ≤ (224242789 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 18423)) (n := 12)
    (lo := (56060697 / 250000000)) (hi := (224242789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8183) = 1/(8183 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-224242789 / 1000000000) (-56060697 / 250000000) (Real.log (8183 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91465861 / 500000000) ≤ -Real.log (20480 / 24591) ∧
    -Real.log (20480 / 24591) ≤ (182931723 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 45071)) (n := 12)
    (lo := (91465861 / 500000000)) (hi := (182931723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24591 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24591 / 20480) = 1/(20480 / 24591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91465861 / 500000000) (182931723 / 1000000000) (Real.log (24591 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24591 / 20480) = -Real.log (20480 / 24591) := by
    rw [show ((24591 / 20480) : ℝ) = ((20480 / 24591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112029749 / 500000000) ≤ -Real.log (16369 / 20480) ∧
    -Real.log (16369 / 20480) ≤ (224059499 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 36849)) (n := 12)
    (lo := (112029749 / 500000000)) (hi := (224059499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16369) = 1/(16369 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224059499 / 1000000000) (-112029749 / 500000000) (Real.log (16369 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (337727029 / 1000000000) ≤ -Real.log (5120 / 7177) ∧
    -Real.log (5120 / 7177) ≤ (33772703 / 100000000) := by
  have h := checkLog_sound (w := (2057 / 12297)) (n := 12)
    (lo := (337727029 / 1000000000)) (hi := (33772703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7177 / 5120) = 1/(5120 / 7177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (337727029 / 1000000000) (33772703 / 100000000) (Real.log (7177 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7177 / 5120) = -Real.log (5120 / 7177) := by
    rw [show ((7177 / 5120) : ℝ) = ((5120 / 7177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (513759611 / 1000000000) ≤ -Real.log (3063 / 5120) ∧
    -Real.log (3063 / 5120) ≤ (128439903 / 250000000) := by
  have h := checkLog_sound (w := (2057 / 8183)) (n := 12)
    (lo := (513759611 / 1000000000)) (hi := (128439903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3063) = 1/(3063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128439903 / 250000000) (-513759611 / 1000000000) (Real.log (3063 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168759003 / 500000000) ≤ -Real.log (10240 / 14351) ∧
    -Real.log (10240 / 14351) ≤ (337518007 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 24591)) (n := 12)
    (lo := (168759003 / 500000000)) (hi := (337518007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14351 / 10240) = 1/(10240 / 14351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168759003 / 500000000) (337518007 / 1000000000) (Real.log (14351 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14351 / 10240) = -Real.log (10240 / 14351) := by
    rw [show ((14351 / 10240) : ℝ) = ((10240 / 14351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (102654003 / 200000000) ≤ -Real.log (6129 / 10240) ∧
    -Real.log (6129 / 10240) ≤ (2004961 / 3906250) := by
  have h := checkLog_sound (w := (4111 / 16369)) (n := 12)
    (lo := (102654003 / 200000000)) (hi := (2004961 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6129) = 1/(6129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2004961 / 3906250) (-102654003 / 200000000) (Real.log (6129 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125738763 / 500000000) ≤ -Real.log (250000 / 321481) ∧
    -Real.log (250000 / 321481) ≤ (251477527 / 1000000000) := by
  have h := checkLog_sound (w := (71481 / 571481)) (n := 12)
    (lo := (125738763 / 500000000)) (hi := (251477527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321481 / 250000) = 1/(250000 / 321481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125738763 / 500000000) (251477527 / 1000000000) (Real.log (321481 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321481 / 250000) = -Real.log (250000 / 321481) := by
    rw [show ((321481 / 250000) : ℝ) = ((250000 / 321481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (336765879 / 1000000000) ≤ -Real.log (178519 / 250000) ∧
    -Real.log (178519 / 250000) ≤ (8419147 / 25000000) := by
  have h := checkLog_sound (w := (71481 / 428519)) (n := 12)
    (lo := (336765879 / 1000000000)) (hi := (8419147 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178519) = 1/(178519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8419147 / 25000000) (-336765879 / 1000000000) (Real.log (178519 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15727697 / 62500000) ≤ -Real.log (1000000 / 1286137) ∧
    -Real.log (1000000 / 1286137) ≤ (251643153 / 1000000000) := by
  have h := checkLog_sound (w := (286137 / 2286137)) (n := 12)
    (lo := (15727697 / 62500000)) (hi := (251643153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286137 / 1000000) = 1/(1000000 / 1286137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15727697 / 62500000) (251643153 / 1000000000) (Real.log (1286137 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286137 / 1000000) = -Real.log (1000000 / 1286137) := by
    rw [show ((1286137 / 1000000) : ℝ) = ((1000000 / 1286137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337064211 / 1000000000) ≤ -Real.log (713863 / 1000000) ∧
    -Real.log (713863 / 1000000) ≤ (84266053 / 250000000) := by
  have h := checkLog_sound (w := (286137 / 1713863)) (n := 12)
    (lo := (337064211 / 1000000000)) (hi := (84266053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713863) = 1/(713863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84266053 / 250000000) (-337064211 / 1000000000) (Real.log (713863 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94011801 / 500000000) ≤ -Real.log (500000 / 603431) ∧
    -Real.log (500000 / 603431) ≤ (188023603 / 1000000000) := by
  have h := checkLog_sound (w := (103431 / 1103431)) (n := 12)
    (lo := (94011801 / 500000000)) (hi := (188023603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603431 / 500000) = 1/(500000 / 603431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94011801 / 500000000) (188023603 / 1000000000) (Real.log (603431 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (603431 / 500000) = -Real.log (500000 / 603431) := by
    rw [show ((603431 / 500000) : ℝ) = ((500000 / 603431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231758049 / 1000000000) ≤ -Real.log (396569 / 500000) ∧
    -Real.log (396569 / 500000) ≤ (4635161 / 20000000) := by
  have h := checkLog_sound (w := (103431 / 896569)) (n := 12)
    (lo := (231758049 / 1000000000)) (hi := (4635161 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396569) = 1/(396569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4635161 / 20000000) (-231758049 / 1000000000) (Real.log (396569 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188156997 / 1000000000) ≤ -Real.log (1000000 / 1207023) ∧
    -Real.log (1000000 / 1207023) ≤ (94078499 / 500000000) := by
  have h := checkLog_sound (w := (207023 / 2207023)) (n := 12)
    (lo := (188156997 / 1000000000)) (hi := (94078499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207023 / 1000000) = 1/(1000000 / 1207023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188156997 / 1000000000) (94078499 / 500000000) (Real.log (1207023 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1207023 / 1000000) = -Real.log (1000000 / 1207023) := by
    rw [show ((1207023 / 1000000) : ℝ) = ((1000000 / 1207023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231961061 / 1000000000) ≤ -Real.log (792977 / 1000000) ∧
    -Real.log (792977 / 1000000) ≤ (115980531 / 500000000) := by
  have h := checkLog_sound (w := (207023 / 1792977)) (n := 12)
    (lo := (231961061 / 1000000000)) (hi := (115980531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792977) = 1/(792977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115980531 / 500000000) (-231961061 / 1000000000) (Real.log (792977 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117648681 / 200000000) ≤ -Real.log (125000000000 / 225102790179) ∧
    -Real.log (125000000000 / 225102790179) ≤ (294121703 / 500000000) := by
  have h := checkLog_sound (w := (100102790179 / 350102790179)) (n := 12)
    (lo := (117648681 / 200000000)) (hi := (294121703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225102790179 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225102790179 / 125000000000) = 1/(125000000000 / 225102790179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117648681 / 200000000) (294121703 / 500000000) (Real.log (225102790179 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (225102790179 / 125000000000) = -Real.log (125000000000 / 225102790179) := by
    rw [show ((225102790179 / 125000000000) : ℝ) = ((125000000000 / 225102790179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (588707363 / 1000000000) ≤ -Real.log (500000000000 / 900829010609) ∧
    -Real.log (500000000000 / 900829010609) ≤ (147176841 / 250000000) := by
  have h := checkLog_sound (w := (400829010609 / 1400829010609)) (n := 12)
    (lo := (588707363 / 1000000000)) (hi := (147176841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900829010609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900829010609 / 500000000000) = 1/(500000000000 / 900829010609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (588707363 / 1000000000) (147176841 / 250000000) (Real.log (900829010609 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (900829010609 / 500000000000) = -Real.log (500000000000 / 900829010609) := by
    rw [show ((900829010609 / 500000000000) : ℝ) = ((500000000000 / 900829010609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104945413 / 250000000) ≤ -Real.log (500000000000 / 760814637553) ∧
    -Real.log (500000000000 / 760814637553) ≤ (419781653 / 1000000000) := by
  have h := checkLog_sound (w := (260814637553 / 1260814637553)) (n := 12)
    (lo := (104945413 / 250000000)) (hi := (419781653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760814637553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760814637553 / 500000000000) = 1/(500000000000 / 760814637553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104945413 / 250000000) (419781653 / 1000000000) (Real.log (760814637553 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760814637553 / 500000000000) = -Real.log (500000000000 / 760814637553) := by
    rw [show ((760814637553 / 500000000000) : ℝ) = ((500000000000 / 760814637553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (210059029 / 500000000) ≤ -Real.log (500000000000 / 761070623739) ∧
    -Real.log (500000000000 / 761070623739) ≤ (420118059 / 1000000000) := by
  have h := checkLog_sound (w := (261070623739 / 1261070623739)) (n := 12)
    (lo := (210059029 / 500000000)) (hi := (420118059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761070623739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761070623739 / 500000000000) = 1/(500000000000 / 761070623739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (210059029 / 500000000) (420118059 / 1000000000) (Real.log (761070623739 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (761070623739 / 500000000000) = -Real.log (500000000000 / 761070623739) := by
    rw [show ((761070623739 / 500000000000) : ℝ) = ((500000000000 / 761070623739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0474

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0475Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0475
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

theorem reflection_log_1_neg : (91465861 / 500000000) ≤ -Real.log (20480 / 24591) ∧
    -Real.log (20480 / 24591) ≤ (182931723 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 45071)) (n := 12)
    (lo := (91465861 / 500000000)) (hi := (182931723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24591 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24591 / 20480) = 1/(20480 / 24591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91465861 / 500000000) (182931723 / 1000000000) (Real.log (24591 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24591 / 20480) = -Real.log (20480 / 24591) := by
    rw [show ((24591 / 20480) : ℝ) = ((20480 / 24591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112029749 / 500000000) ≤ -Real.log (16369 / 20480) ∧
    -Real.log (16369 / 20480) ≤ (224059499 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 36849)) (n := 12)
    (lo := (112029749 / 500000000)) (hi := (224059499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16369) = 1/(16369 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-224059499 / 1000000000) (-112029749 / 500000000) (Real.log (16369 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91404859 / 500000000) ≤ -Real.log (5120 / 6147) ∧
    -Real.log (5120 / 6147) ≤ (182809719 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 11267)) (n := 12)
    (lo := (91404859 / 500000000)) (hi := (182809719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6147 / 5120) = 1/(5120 / 6147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91404859 / 500000000) (182809719 / 1000000000) (Real.log (6147 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6147 / 5120) = -Real.log (5120 / 6147) := by
    rw [show ((6147 / 5120) : ℝ) = ((5120 / 6147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223876241 / 1000000000) ≤ -Real.log (4093 / 5120) ∧
    -Real.log (4093 / 5120) ≤ (111938121 / 500000000) := by
  have h := checkLog_sound (w := (1027 / 9213)) (n := 12)
    (lo := (223876241 / 1000000000)) (hi := (111938121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4093) = 1/(4093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111938121 / 500000000) (-223876241 / 1000000000) (Real.log (4093 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168759003 / 500000000) ≤ -Real.log (10240 / 14351) ∧
    -Real.log (10240 / 14351) ≤ (337518007 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 24591)) (n := 12)
    (lo := (168759003 / 500000000)) (hi := (337518007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14351 / 10240) = 1/(10240 / 14351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168759003 / 500000000) (337518007 / 1000000000) (Real.log (14351 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14351 / 10240) = -Real.log (10240 / 14351) := by
    rw [show ((14351 / 10240) : ℝ) = ((10240 / 14351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (102654003 / 200000000) ≤ -Real.log (6129 / 10240) ∧
    -Real.log (6129 / 10240) ≤ (2004961 / 3906250) := by
  have h := checkLog_sound (w := (4111 / 16369)) (n := 12)
    (lo := (102654003 / 200000000)) (hi := (2004961 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6129) = 1/(6129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2004961 / 3906250) (-102654003 / 200000000) (Real.log (6129 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16865447 / 50000000) ≤ -Real.log (2560 / 3587) ∧
    -Real.log (2560 / 3587) ≤ (337308941 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 6147)) (n := 12)
    (lo := (16865447 / 50000000)) (hi := (337308941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3587 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3587 / 2560) = 1/(2560 / 3587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16865447 / 50000000) (337308941 / 1000000000) (Real.log (3587 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3587 / 2560) = -Real.log (2560 / 3587) := by
    rw [show ((3587 / 2560) : ℝ) = ((2560 / 3587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256390329 / 500000000) ≤ -Real.log (1533 / 2560) ∧
    -Real.log (1533 / 2560) ≤ (512780659 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 4093)) (n := 12)
    (lo := (256390329 / 500000000)) (hi := (512780659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1533) = 1/(1533 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-512780659 / 1000000000) (-256390329 / 500000000) (Real.log (1533 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5026253 / 20000000) ≤ -Real.log (62500 / 80357) ∧
    -Real.log (62500 / 80357) ≤ (251312651 / 1000000000) := by
  have h := checkLog_sound (w := (17857 / 142857)) (n := 12)
    (lo := (5026253 / 20000000)) (hi := (251312651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80357 / 62500) = 1/(62500 / 80357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5026253 / 20000000) (251312651 / 1000000000) (Real.log (80357 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (80357 / 62500) = -Real.log (62500 / 80357) := by
    rw [show ((80357 / 62500) : ℝ) = ((62500 / 80357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84117259 / 250000000) ≤ -Real.log (44643 / 62500) ∧
    -Real.log (44643 / 62500) ≤ (336469037 / 1000000000) := by
  have h := checkLog_sound (w := (17857 / 107143)) (n := 12)
    (lo := (84117259 / 250000000)) (hi := (336469037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44643) = 1/(44643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-336469037 / 1000000000) (-84117259 / 250000000) (Real.log (44643 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251478303 / 1000000000) ≤ -Real.log (40000 / 51437) ∧
    -Real.log (40000 / 51437) ≤ (7858697 / 31250000) := by
  have h := checkLog_sound (w := (11437 / 91437)) (n := 12)
    (lo := (251478303 / 1000000000)) (hi := (7858697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51437 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51437 / 40000) = 1/(40000 / 51437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251478303 / 1000000000) (7858697 / 31250000) (Real.log (51437 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (51437 / 40000) = -Real.log (40000 / 51437) := by
    rw [show ((51437 / 40000) : ℝ) = ((40000 / 51437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4209591 / 12500000) ≤ -Real.log (28563 / 40000) ∧
    -Real.log (28563 / 40000) ≤ (336767281 / 1000000000) := by
  have h := checkLog_sound (w := (11437 / 68563)) (n := 12)
    (lo := (4209591 / 12500000)) (hi := (336767281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28563) = 1/(28563 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336767281 / 1000000000) (-4209591 / 12500000) (Real.log (28563 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (187890189 / 1000000000) ≤ -Real.log (1000000 / 1206701) ∧
    -Real.log (1000000 / 1206701) ≤ (18789019 / 100000000) := by
  have h := checkLog_sound (w := (206701 / 2206701)) (n := 12)
    (lo := (187890189 / 1000000000)) (hi := (18789019 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206701 / 1000000) = 1/(1000000 / 1206701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (187890189 / 1000000000) (18789019 / 100000000) (Real.log (1206701 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206701 / 1000000) = -Real.log (1000000 / 1206701) := by
    rw [show ((1206701 / 1000000) : ℝ) = ((1000000 / 1206701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231555079 / 1000000000) ≤ -Real.log (793299 / 1000000) ∧
    -Real.log (793299 / 1000000) ≤ (5788877 / 25000000) := by
  have h := checkLog_sound (w := (206701 / 1793299)) (n := 12)
    (lo := (231555079 / 1000000000)) (hi := (5788877 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793299) = 1/(793299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5788877 / 25000000) (-231555079 / 1000000000) (Real.log (793299 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188024431 / 1000000000) ≤ -Real.log (1000000 / 1206863) ∧
    -Real.log (1000000 / 1206863) ≤ (11751527 / 62500000) := by
  have h := checkLog_sound (w := (206863 / 2206863)) (n := 12)
    (lo := (188024431 / 1000000000)) (hi := (11751527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206863 / 1000000) = 1/(1000000 / 1206863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188024431 / 1000000000) (11751527 / 62500000) (Real.log (1206863 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1206863 / 1000000) = -Real.log (1000000 / 1206863) := by
    rw [show ((1206863 / 1000000) : ℝ) = ((1000000 / 1206863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23175931 / 100000000) ≤ -Real.log (793137 / 1000000) ∧
    -Real.log (793137 / 1000000) ≤ (231759311 / 1000000000) := by
  have h := checkLog_sound (w := (206863 / 1793137)) (n := 12)
    (lo := (23175931 / 100000000)) (hi := (231759311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793137) = 1/(793137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-231759311 / 1000000000) (-23175931 / 100000000) (Real.log (793137 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (587781687 / 1000000000) ≤ -Real.log (250000000000 / 449997760007) ∧
    -Real.log (250000000000 / 449997760007) ≤ (73472711 / 125000000) := by
  have h := checkLog_sound (w := (199997760007 / 699997760007)) (n := 12)
    (lo := (587781687 / 1000000000)) (hi := (73472711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449997760007 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449997760007 / 250000000000) = 1/(250000000000 / 449997760007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (587781687 / 1000000000) (73472711 / 125000000) (Real.log (449997760007 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449997760007 / 250000000000) = -Real.log (250000000000 / 449997760007) := by
    rw [show ((449997760007 / 250000000000) : ℝ) = ((250000000000 / 449997760007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (588245583 / 1000000000) ≤ -Real.log (500000000000 / 900413121871) ∧
    -Real.log (500000000000 / 900413121871) ≤ (36765349 / 62500000) := by
  have h := checkLog_sound (w := (400413121871 / 1400413121871)) (n := 12)
    (lo := (588245583 / 1000000000)) (hi := (36765349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900413121871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900413121871 / 500000000000) = 1/(500000000000 / 900413121871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (588245583 / 1000000000) (36765349 / 62500000) (Real.log (900413121871 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (900413121871 / 500000000000) = -Real.log (500000000000 / 900413121871) := by
    rw [show ((900413121871 / 500000000000) : ℝ) = ((500000000000 / 900413121871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (419445269 / 1000000000) ≤ -Real.log (500000000000 / 760558755273) ∧
    -Real.log (500000000000 / 760558755273) ≤ (41944527 / 100000000) := by
  have h := checkLog_sound (w := (260558755273 / 1260558755273)) (n := 12)
    (lo := (419445269 / 1000000000)) (hi := (41944527 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760558755273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760558755273 / 500000000000) = 1/(500000000000 / 760558755273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (419445269 / 1000000000) (41944527 / 100000000) (Real.log (760558755273 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760558755273 / 500000000000) = -Real.log (500000000000 / 760558755273) := by
    rw [show ((760558755273 / 500000000000) : ℝ) = ((500000000000 / 760558755273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (419783741 / 1000000000) ≤ -Real.log (50000000000 / 76081622721) ∧
    -Real.log (50000000000 / 76081622721) ≤ (209891871 / 500000000) := by
  have h := checkLog_sound (w := (26081622721 / 126081622721)) (n := 12)
    (lo := (419783741 / 1000000000)) (hi := (209891871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76081622721 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76081622721 / 50000000000) = 1/(50000000000 / 76081622721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (419783741 / 1000000000) (209891871 / 500000000) (Real.log (76081622721 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76081622721 / 50000000000) = -Real.log (50000000000 / 76081622721) := by
    rw [show ((76081622721 / 50000000000) : ℝ) = ((50000000000 / 76081622721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0475

end


