-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell189Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell189Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:51:30.629261+00:00
-- url     : https://prove2.me/theorems/cf24434d-30f8-42d6-96bf-3a35b74b1c8b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell192Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell193Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell194Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell195Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell196Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell192Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell193Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell194Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell195Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell196Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell192Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell193Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell194Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell195Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell196Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell189Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell190Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell191Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell192Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell193Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell194Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell195Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell196Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189
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

theorem reflection_log_1_neg : (61692157 / 200000000) ≤ -Real.log (512 / 697) ∧
    -Real.log (512 / 697) ≤ (154230393 / 500000000) := by
  have h := checkLog_sound (w := (185 / 1209)) (n := 12)
    (lo := (61692157 / 200000000)) (hi := (154230393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 512) = 1/(512 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61692157 / 200000000) (154230393 / 500000000) (Real.log (697 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (697 / 512) = -Real.log (512 / 697) := by
    rw [show ((697 / 512) : ℝ) = ((512 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224182227 / 500000000) ≤ -Real.log (327 / 512) ∧
    -Real.log (327 / 512) ≤ (89672891 / 200000000) := by
  have h := checkLog_sound (w := (185 / 839)) (n := 12)
    (lo := (224182227 / 500000000)) (hi := (89672891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 327) = 1/(327 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) (Real.log (327 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (77007569 / 250000000) ≤ -Real.log (5120 / 6967) ∧
    -Real.log (5120 / 6967) ≤ (308030277 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 12087)) (n := 12)
    (lo := (77007569 / 250000000)) (hi := (308030277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6967 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6967 / 5120) = 1/(5120 / 6967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (77007569 / 250000000) (308030277 / 1000000000) (Real.log (6967 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6967 / 5120) = -Real.log (5120 / 6967) := by
    rw [show ((6967 / 5120) : ℝ) = ((5120 / 6967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (447447443 / 1000000000) ≤ -Real.log (3273 / 5120) ∧
    -Real.log (3273 / 5120) ≤ (111861861 / 250000000) := by
  have h := checkLog_sound (w := (1847 / 8393)) (n := 12)
    (lo := (447447443 / 1000000000)) (hi := (111861861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3273) = 1/(3273 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111861861 / 250000000) (-447447443 / 1000000000) (Real.log (3273 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (114183343 / 500000000) ≤ -Real.log (500000 / 628273) ∧
    -Real.log (500000 / 628273) ≤ (228366687 / 1000000000) := by
  have h := checkLog_sound (w := (128273 / 1128273)) (n := 12)
    (lo := (114183343 / 500000000)) (hi := (228366687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628273 / 500000) = 1/(500000 / 628273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (114183343 / 500000000) (228366687 / 1000000000) (Real.log (628273 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (628273 / 500000) = -Real.log (500000 / 628273) := by
    rw [show ((628273 / 500000) : ℝ) = ((500000 / 628273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2316003 / 7812500) ≤ -Real.log (371727 / 500000) ∧
    -Real.log (371727 / 500000) ≤ (59289677 / 200000000) := by
  have h := checkLog_sound (w := (128273 / 871727)) (n := 12)
    (lo := (2316003 / 7812500)) (hi := (59289677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371727) = 1/(371727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59289677 / 200000000) (-2316003 / 7812500) (Real.log (371727 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (228703267 / 1000000000) ≤ -Real.log (1000000 / 1256969) ∧
    -Real.log (1000000 / 1256969) ≤ (57175817 / 250000000) := by
  have h := checkLog_sound (w := (256969 / 2256969)) (n := 12)
    (lo := (228703267 / 1000000000)) (hi := (57175817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256969 / 1000000) = 1/(1000000 / 1256969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (228703267 / 1000000000) (57175817 / 250000000) (Real.log (1256969 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1256969 / 1000000) = -Real.log (1000000 / 1256969) := by
    rw [show ((1256969 / 1000000) : ℝ) = ((1000000 / 1256969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (37127189 / 125000000) ≤ -Real.log (743031 / 1000000) ∧
    -Real.log (743031 / 1000000) ≤ (297017513 / 1000000000) := by
  have h := checkLog_sound (w := (256969 / 1743031)) (n := 12)
    (lo := (37127189 / 125000000)) (hi := (297017513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743031) = 1/(743031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-297017513 / 1000000000) (-37127189 / 125000000) (Real.log (743031 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169552039 / 1000000000) ≤ -Real.log (500000 / 592387) ∧
    -Real.log (500000 / 592387) ≤ (4238801 / 25000000) := by
  have h := checkLog_sound (w := (92387 / 1092387)) (n := 12)
    (lo := (169552039 / 1000000000)) (hi := (4238801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592387 / 500000) = 1/(500000 / 592387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169552039 / 1000000000) (4238801 / 25000000) (Real.log (592387 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (592387 / 500000) = -Real.log (500000 / 592387) := by
    rw [show ((592387 / 500000) : ℝ) = ((500000 / 592387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (204289903 / 1000000000) ≤ -Real.log (407613 / 500000) ∧
    -Real.log (407613 / 500000) ≤ (12768119 / 62500000) := by
  have h := checkLog_sound (w := (92387 / 907613)) (n := 12)
    (lo := (204289903 / 1000000000)) (hi := (12768119 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407613) = 1/(407613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12768119 / 62500000) (-204289903 / 1000000000) (Real.log (407613 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169818721 / 1000000000) ≤ -Real.log (100000 / 118509) ∧
    -Real.log (100000 / 118509) ≤ (84909361 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 218509)) (n := 12)
    (lo := (169818721 / 1000000000)) (hi := (84909361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118509 / 100000) = 1/(100000 / 118509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169818721 / 1000000000) (84909361 / 500000000) (Real.log (118509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (118509 / 100000) = -Real.log (100000 / 118509) := by
    rw [show ((118509 / 100000) : ℝ) = ((100000 / 118509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (204677601 / 1000000000) ≤ -Real.log (81491 / 100000) ∧
    -Real.log (81491 / 100000) ≤ (102338801 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 181491)) (n := 12)
    (lo := (204677601 / 1000000000)) (hi := (102338801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81491) = 1/(81491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) (Real.log (81491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (755477719 / 1000000000) ≤ -Real.log (500000000000 / 1064314084937) ∧
    -Real.log (500000000000 / 1064314084937) ≤ (755477721 / 1000000000) := by
  have h := checkLog_sound (w := (64314084937 / 2064314084937)) (n := 12)
    (lo := (62330539 / 1000000000)) (hi := (3116527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064314084937 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064314084937 / 1000000000000) = 1/(500000000000 / 1064314084937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (755477719 / 1000000000) (755477721 / 1000000000) (Real.log (1064314084937 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1064314084937 / 500000000000) = -Real.log (500000000000 / 1064314084937) := by
    rw [show ((1064314084937 / 500000000000) : ℝ) = ((500000000000 / 1064314084937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (756825239 / 1000000000) ≤ -Real.log (20000000000 / 42629969419) ∧
    -Real.log (20000000000 / 42629969419) ≤ (756825241 / 1000000000) := by
  have h := checkLog_sound (w := (2629969419 / 82629969419)) (n := 12)
    (lo := (63678059 / 1000000000)) (hi := (3183903 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42629969419 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42629969419 / 40000000000) = 1/(20000000000 / 42629969419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (756825239 / 1000000000) (756825241 / 1000000000) (Real.log (42629969419 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42629969419 / 20000000000) = -Real.log (20000000000 / 42629969419) := by
    rw [show ((42629969419 / 20000000000) : ℝ) = ((20000000000 / 42629969419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (524815071 / 1000000000) ≤ -Real.log (250000000000 / 422536565813) ∧
    -Real.log (250000000000 / 422536565813) ≤ (16400471 / 31250000) := by
  have h := checkLog_sound (w := (172536565813 / 672536565813)) (n := 12)
    (lo := (524815071 / 1000000000)) (hi := (16400471 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422536565813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422536565813 / 250000000000) = 1/(250000000000 / 422536565813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (524815071 / 1000000000) (16400471 / 31250000) (Real.log (422536565813 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (422536565813 / 250000000000) = -Real.log (250000000000 / 422536565813) := by
    rw [show ((422536565813 / 250000000000) : ℝ) = ((250000000000 / 422536565813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (525720779 / 1000000000) ≤ -Real.log (3906250000 / 6608116157) ∧
    -Real.log (3906250000 / 6608116157) ≤ (26286039 / 50000000) := by
  have h := checkLog_sound (w := (2701866157 / 10514366157)) (n := 12)
    (lo := (525720779 / 1000000000)) (hi := (26286039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6608116157 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6608116157 / 3906250000) = 1/(3906250000 / 6608116157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (525720779 / 1000000000) (26286039 / 50000000) (Real.log (6608116157 / 3906250000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6608116157 / 3906250000) = -Real.log (3906250000 / 6608116157) := by
    rw [show ((6608116157 / 3906250000) : ℝ) = ((3906250000 / 6608116157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (186920971 / 500000000) ≤ -Real.log (500000000000 / 726653713203) ∧
    -Real.log (500000000000 / 726653713203) ≤ (373841943 / 1000000000) := by
  have h := checkLog_sound (w := (226653713203 / 1226653713203)) (n := 12)
    (lo := (186920971 / 500000000)) (hi := (373841943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726653713203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726653713203 / 500000000000) = 1/(500000000000 / 726653713203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (186920971 / 500000000) (373841943 / 1000000000) (Real.log (726653713203 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (726653713203 / 500000000000) = -Real.log (500000000000 / 726653713203) := by
    rw [show ((726653713203 / 500000000000) : ℝ) = ((500000000000 / 726653713203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (187248161 / 500000000) ≤ -Real.log (500000000000 / 727129376251) ∧
    -Real.log (500000000000 / 727129376251) ≤ (374496323 / 1000000000) := by
  have h := checkLog_sound (w := (227129376251 / 1227129376251)) (n := 12)
    (lo := (187248161 / 500000000)) (hi := (374496323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727129376251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727129376251 / 500000000000) = 1/(500000000000 / 727129376251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (187248161 / 500000000) (374496323 / 1000000000) (Real.log (727129376251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (727129376251 / 500000000000) = -Real.log (500000000000 / 727129376251) := by
    rw [show ((727129376251 / 500000000000) : ℝ) = ((500000000000 / 727129376251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54467 / 1562500) ≤ -Real.log (9657416919 / 10000000000) ∧
    -Real.log (9657416919 / 10000000000) ≤ (34858881 / 1000000000) := by
  have h := checkLog_sound (w := (342583081 / 19657416919)) (n := 12)
    (lo := (54467 / 1562500)) (hi := (34858881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9657416919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9657416919) = 1/(9657416919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34858881 / 1000000000) (-54467 / 1562500) (Real.log (9657416919 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4342233 / 125000000) ≤ -Real.log (241464642231 / 250000000000) ∧
    -Real.log (241464642231 / 250000000000) ≤ (6947573 / 200000000) := by
  have h := checkLog_sound (w := (8535357769 / 491464642231)) (n := 12)
    (lo := (4342233 / 125000000)) (hi := (6947573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241464642231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241464642231) = 1/(241464642231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6947573 / 200000000) (-4342233 / 125000000) (Real.log (241464642231 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190
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

theorem reflection_log_1_neg : (308891109 / 1000000000) ≤ -Real.log (5120 / 6973) ∧
    -Real.log (5120 / 6973) ≤ (30889111 / 100000000) := by
  have h := checkLog_sound (w := (1853 / 12093)) (n := 12)
    (lo := (308891109 / 1000000000)) (hi := (30889111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6973 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6973 / 5120) = 1/(5120 / 6973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (308891109 / 1000000000) (30889111 / 100000000) (Real.log (6973 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6973 / 5120) = -Real.log (5120 / 6973) := by
    rw [show ((6973 / 5120) : ℝ) = ((5120 / 6973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224641153 / 500000000) ≤ -Real.log (3267 / 5120) ∧
    -Real.log (3267 / 5120) ≤ (449282307 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 8387)) (n := 12)
    (lo := (224641153 / 500000000)) (hi := (449282307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3267) = 1/(3267 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) (Real.log (3267 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61692157 / 200000000) ≤ -Real.log (512 / 697) ∧
    -Real.log (512 / 697) ≤ (154230393 / 500000000) := by
  have h := checkLog_sound (w := (185 / 1209)) (n := 12)
    (lo := (61692157 / 200000000)) (hi := (154230393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 512) = 1/(512 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61692157 / 200000000) (154230393 / 500000000) (Real.log (697 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (697 / 512) = -Real.log (512 / 697) := by
    rw [show ((697 / 512) : ℝ) = ((512 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224182227 / 500000000) ≤ -Real.log (327 / 512) ∧
    -Real.log (327 / 512) ≤ (89672891 / 200000000) := by
  have h := checkLog_sound (w := (185 / 839)) (n := 12)
    (lo := (224182227 / 500000000)) (hi := (89672891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 327) = 1/(327 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) (Real.log (327 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (228702471 / 1000000000) ≤ -Real.log (125000 / 157121) ∧
    -Real.log (125000 / 157121) ≤ (28587809 / 125000000) := by
  have h := checkLog_sound (w := (32121 / 282121)) (n := 12)
    (lo := (228702471 / 1000000000)) (hi := (28587809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157121 / 125000) = 1/(125000 / 157121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (228702471 / 1000000000) (28587809 / 125000000) (Real.log (157121 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (157121 / 125000) = -Real.log (125000 / 157121) := by
    rw [show ((157121 / 125000) : ℝ) = ((125000 / 157121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (148508083 / 500000000) ≤ -Real.log (92879 / 125000) ∧
    -Real.log (92879 / 125000) ≤ (297016167 / 1000000000) := by
  have h := checkLog_sound (w := (32121 / 217879)) (n := 12)
    (lo := (148508083 / 500000000)) (hi := (297016167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92879) = 1/(92879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-297016167 / 1000000000) (-148508083 / 500000000) (Real.log (92879 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229038939 / 1000000000) ≤ -Real.log (1000000 / 1257391) ∧
    -Real.log (1000000 / 1257391) ≤ (11451947 / 50000000) := by
  have h := checkLog_sound (w := (257391 / 2257391)) (n := 12)
    (lo := (229038939 / 1000000000)) (hi := (11451947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257391 / 1000000) = 1/(1000000 / 1257391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229038939 / 1000000000) (11451947 / 50000000) (Real.log (1257391 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1257391 / 1000000) = -Real.log (1000000 / 1257391) := by
    rw [show ((1257391 / 1000000) : ℝ) = ((1000000 / 1257391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (297585617 / 1000000000) ≤ -Real.log (742609 / 1000000) ∧
    -Real.log (742609 / 1000000) ≤ (148792809 / 500000000) := by
  have h := checkLog_sound (w := (257391 / 1742609)) (n := 12)
    (lo := (297585617 / 1000000000)) (hi := (148792809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742609) = 1/(742609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-148792809 / 500000000) (-297585617 / 1000000000) (Real.log (742609 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169817877 / 1000000000) ≤ -Real.log (1000000 / 1185089) ∧
    -Real.log (1000000 / 1185089) ≤ (84908939 / 500000000) := by
  have h := checkLog_sound (w := (185089 / 2185089)) (n := 12)
    (lo := (169817877 / 1000000000)) (hi := (84908939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185089 / 1000000) = 1/(1000000 / 1185089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169817877 / 1000000000) (84908939 / 500000000) (Real.log (1185089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1185089 / 1000000) = -Real.log (1000000 / 1185089) := by
    rw [show ((1185089 / 1000000) : ℝ) = ((1000000 / 1185089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102338187 / 500000000) ≤ -Real.log (814911 / 1000000) ∧
    -Real.log (814911 / 1000000) ≤ (1637411 / 8000000) := by
  have h := checkLog_sound (w := (185089 / 1814911)) (n := 12)
    (lo := (102338187 / 500000000)) (hi := (1637411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814911) = 1/(814911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1637411 / 8000000) (-102338187 / 500000000) (Real.log (814911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21260561 / 125000000) ≤ -Real.log (200000 / 237081) ∧
    -Real.log (200000 / 237081) ≤ (170084489 / 1000000000) := by
  have h := checkLog_sound (w := (37081 / 437081)) (n := 12)
    (lo := (21260561 / 125000000)) (hi := (170084489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237081 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237081 / 200000) = 1/(200000 / 237081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21260561 / 125000000) (170084489 / 1000000000) (Real.log (237081 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (237081 / 200000) = -Real.log (200000 / 237081) := by
    rw [show ((237081 / 200000) : ℝ) = ((200000 / 237081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (205064221 / 1000000000) ≤ -Real.log (162919 / 200000) ∧
    -Real.log (162919 / 200000) ≤ (102532111 / 500000000) := by
  have h := checkLog_sound (w := (37081 / 362919)) (n := 12)
    (lo := (205064221 / 1000000000)) (hi := (102532111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162919) = 1/(162919 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-102532111 / 500000000) (-205064221 / 1000000000) (Real.log (162919 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (756825239 / 1000000000) ≤ -Real.log (250000000000 / 532874617737) ∧
    -Real.log (250000000000 / 532874617737) ≤ (756825241 / 1000000000) := by
  have h := checkLog_sound (w := (32874617737 / 1032874617737)) (n := 12)
    (lo := (63678059 / 1000000000)) (hi := (3183903 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532874617737 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532874617737 / 500000000000) = 1/(250000000000 / 532874617737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (756825239 / 1000000000) (756825241 / 1000000000) (Real.log (532874617737 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (532874617737 / 250000000000) = -Real.log (250000000000 / 532874617737) := by
    rw [show ((532874617737 / 250000000000) : ℝ) = ((250000000000 / 532874617737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151634683 / 200000000) ≤ -Real.log (500000000000 / 1067187021733) ∧
    -Real.log (500000000000 / 1067187021733) ≤ (758173417 / 1000000000) := by
  have h := checkLog_sound (w := (67187021733 / 2067187021733)) (n := 12)
    (lo := (13005247 / 200000000)) (hi := (16256559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067187021733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067187021733 / 1000000000000) = 1/(500000000000 / 1067187021733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151634683 / 200000000) (758173417 / 1000000000) (Real.log (1067187021733 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1067187021733 / 500000000000) = -Real.log (500000000000 / 1067187021733) := by
    rw [show ((1067187021733 / 500000000000) : ℝ) = ((500000000000 / 1067187021733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (262859319 / 500000000) ≤ -Real.log (100000000000 / 169167411363) ∧
    -Real.log (100000000000 / 169167411363) ≤ (525718639 / 1000000000) := by
  have h := checkLog_sound (w := (69167411363 / 269167411363)) (n := 12)
    (lo := (262859319 / 500000000)) (hi := (525718639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169167411363 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169167411363 / 100000000000) = 1/(100000000000 / 169167411363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (262859319 / 500000000) (525718639 / 1000000000) (Real.log (169167411363 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (169167411363 / 100000000000) = -Real.log (100000000000 / 169167411363) := by
    rw [show ((169167411363 / 100000000000) : ℝ) = ((100000000000 / 169167411363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (526624557 / 1000000000) ≤ -Real.log (50000000000 / 84660366357) ∧
    -Real.log (50000000000 / 84660366357) ≤ (263312279 / 500000000) := by
  have h := checkLog_sound (w := (34660366357 / 134660366357)) (n := 12)
    (lo := (526624557 / 1000000000)) (hi := (263312279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84660366357 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84660366357 / 50000000000) = 1/(50000000000 / 84660366357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (526624557 / 1000000000) (263312279 / 500000000) (Real.log (84660366357 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (84660366357 / 50000000000) = -Real.log (50000000000 / 84660366357) := by
    rw [show ((84660366357 / 50000000000) : ℝ) = ((50000000000 / 84660366357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (374494251 / 1000000000) ≤ -Real.log (100000000000 / 145425574081) ∧
    -Real.log (100000000000 / 145425574081) ≤ (93623563 / 250000000) := by
  have h := checkLog_sound (w := (45425574081 / 245425574081)) (n := 12)
    (lo := (374494251 / 1000000000)) (hi := (93623563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145425574081 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145425574081 / 100000000000) = 1/(100000000000 / 145425574081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (374494251 / 1000000000) (93623563 / 250000000) (Real.log (145425574081 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145425574081 / 100000000000) = -Real.log (100000000000 / 145425574081) := by
    rw [show ((145425574081 / 100000000000) : ℝ) = ((100000000000 / 145425574081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37514871 / 100000000) ≤ -Real.log (250000000000 / 363801950663) ∧
    -Real.log (250000000000 / 363801950663) ≤ (375148711 / 1000000000) := by
  have h := checkLog_sound (w := (113801950663 / 613801950663)) (n := 12)
    (lo := (37514871 / 100000000)) (hi := (375148711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363801950663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363801950663 / 250000000000) = 1/(250000000000 / 363801950663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37514871 / 100000000) (375148711 / 1000000000) (Real.log (363801950663 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (363801950663 / 250000000000) = -Real.log (250000000000 / 363801950663) := by
    rw [show ((363801950663 / 250000000000) : ℝ) = ((250000000000 / 363801950663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34979733 / 1000000000) ≤ -Real.log (38624999439 / 40000000000) ∧
    -Real.log (38624999439 / 40000000000) ≤ (17489867 / 500000000) := by
  have h := checkLog_sound (w := (1375000561 / 78624999439)) (n := 12)
    (lo := (34979733 / 1000000000)) (hi := (17489867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38624999439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38624999439) = 1/(38624999439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17489867 / 500000000) (-34979733 / 1000000000) (Real.log (38624999439 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (68083 / 1953125) ≤ -Real.log (965742062079 / 1000000000000) ∧
    -Real.log (965742062079 / 1000000000000) ≤ (34858497 / 1000000000) := by
  have h := checkLog_sound (w := (34257937921 / 1965742062079)) (n := 12)
    (lo := (68083 / 1953125)) (hi := (34858497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965742062079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965742062079) = 1/(965742062079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34858497 / 1000000000) (-68083 / 1953125) (Real.log (965742062079 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191
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

theorem reflection_log_1_neg : (309321247 / 1000000000) ≤ -Real.log (80 / 109) ∧
    -Real.log (80 / 109) ≤ (9666289 / 31250000) := by
  have h := checkLog_sound (w := (29 / 189)) (n := 12)
    (lo := (309321247 / 1000000000)) (hi := (9666289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109 / 80) = 1/(80 / 109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (309321247 / 1000000000) (9666289 / 31250000) (Real.log (109 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (109 / 80) = -Real.log (80 / 109) := by
    rw [show ((109 / 80) : ℝ) = ((80 / 109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (450201001 / 1000000000) ≤ -Real.log (51 / 80) ∧
    -Real.log (51 / 80) ≤ (225100501 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 51) = 1/(51 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-225100501 / 500000000) (-450201001 / 1000000000) (Real.log (51 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (308891109 / 1000000000) ≤ -Real.log (5120 / 6973) ∧
    -Real.log (5120 / 6973) ≤ (30889111 / 100000000) := by
  have h := checkLog_sound (w := (1853 / 12093)) (n := 12)
    (lo := (308891109 / 1000000000)) (hi := (30889111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6973 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6973 / 5120) = 1/(5120 / 6973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (308891109 / 1000000000) (30889111 / 100000000) (Real.log (6973 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6973 / 5120) = -Real.log (5120 / 6973) := by
    rw [show ((6973 / 5120) : ℝ) = ((5120 / 6973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224641153 / 500000000) ≤ -Real.log (3267 / 5120) ∧
    -Real.log (3267 / 5120) ≤ (449282307 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 8387)) (n := 12)
    (lo := (224641153 / 500000000)) (hi := (449282307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3267) = 1/(3267 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) (Real.log (3267 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (57259337 / 250000000) ≤ -Real.log (1000000 / 1257389) ∧
    -Real.log (1000000 / 1257389) ≤ (229037349 / 1000000000) := by
  have h := checkLog_sound (w := (257389 / 2257389)) (n := 12)
    (lo := (57259337 / 250000000)) (hi := (229037349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257389 / 1000000) = 1/(1000000 / 1257389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (57259337 / 250000000) (229037349 / 1000000000) (Real.log (1257389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1257389 / 1000000) = -Real.log (1000000 / 1257389) := by
    rw [show ((1257389 / 1000000) : ℝ) = ((1000000 / 1257389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74395731 / 250000000) ≤ -Real.log (742611 / 1000000) ∧
    -Real.log (742611 / 1000000) ≤ (11903317 / 40000000) := by
  have h := checkLog_sound (w := (257389 / 1742611)) (n := 12)
    (lo := (74395731 / 250000000)) (hi := (11903317 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742611) = 1/(742611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11903317 / 40000000) (-74395731 / 250000000) (Real.log (742611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229373703 / 1000000000) ≤ -Real.log (250000 / 314453) ∧
    -Real.log (250000 / 314453) ≤ (28671713 / 125000000) := by
  have h := checkLog_sound (w := (64453 / 564453)) (n := 12)
    (lo := (229373703 / 1000000000)) (hi := (28671713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314453 / 250000) = 1/(250000 / 314453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229373703 / 1000000000) (28671713 / 125000000) (Real.log (314453 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (314453 / 250000) = -Real.log (250000 / 314453) := by
    rw [show ((314453 / 250000) : ℝ) = ((250000 / 314453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (149076349 / 500000000) ≤ -Real.log (185547 / 250000) ∧
    -Real.log (185547 / 250000) ≤ (298152699 / 1000000000) := by
  have h := checkLog_sound (w := (64453 / 435547)) (n := 12)
    (lo := (149076349 / 500000000)) (hi := (298152699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185547) = 1/(185547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-298152699 / 1000000000) (-149076349 / 500000000) (Real.log (185547 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42520911 / 250000000) ≤ -Real.log (250000 / 296351) ∧
    -Real.log (250000 / 296351) ≤ (34016729 / 200000000) := by
  have h := checkLog_sound (w := (46351 / 546351)) (n := 12)
    (lo := (42520911 / 250000000)) (hi := (34016729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296351 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296351 / 250000) = 1/(250000 / 296351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42520911 / 250000000) (34016729 / 200000000) (Real.log (296351 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296351 / 250000) = -Real.log (250000 / 296351) := by
    rw [show ((296351 / 250000) : ℝ) = ((250000 / 296351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102531497 / 500000000) ≤ -Real.log (203649 / 250000) ∧
    -Real.log (203649 / 250000) ≤ (41012599 / 200000000) := by
  have h := checkLog_sound (w := (46351 / 453649)) (n := 12)
    (lo := (102531497 / 500000000)) (hi := (41012599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203649) = 1/(203649 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41012599 / 200000000) (-102531497 / 500000000) (Real.log (203649 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34070037 / 200000000) ≤ -Real.log (25000 / 29643) ∧
    -Real.log (25000 / 29643) ≤ (85175093 / 500000000) := by
  have h := checkLog_sound (w := (4643 / 54643)) (n := 12)
    (lo := (34070037 / 200000000)) (hi := (85175093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29643 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29643 / 25000) = 1/(25000 / 29643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34070037 / 200000000) (85175093 / 500000000) (Real.log (29643 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (29643 / 25000) = -Real.log (25000 / 29643) := by
    rw [show ((29643 / 25000) : ℝ) = ((25000 / 29643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (205450991 / 1000000000) ≤ -Real.log (20357 / 25000) ∧
    -Real.log (20357 / 25000) ≤ (12840687 / 62500000) := by
  have h := checkLog_sound (w := (4643 / 45357)) (n := 12)
    (lo := (205450991 / 1000000000)) (hi := (12840687 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20357) = 1/(20357 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12840687 / 62500000) (-205450991 / 1000000000) (Real.log (20357 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151634683 / 200000000) ≤ -Real.log (125000000000 / 266796755433) ∧
    -Real.log (125000000000 / 266796755433) ≤ (758173417 / 1000000000) := by
  have h := checkLog_sound (w := (16796755433 / 516796755433)) (n := 12)
    (lo := (13005247 / 200000000)) (hi := (16256559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266796755433 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(266796755433 / 250000000000) = 1/(125000000000 / 266796755433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151634683 / 200000000) (758173417 / 1000000000) (Real.log (266796755433 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (266796755433 / 125000000000) = -Real.log (125000000000 / 266796755433) := by
    rw [show ((266796755433 / 125000000000) : ℝ) = ((125000000000 / 266796755433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (94940281 / 125000000) ≤ -Real.log (500000000000 / 1068627450981) ∧
    -Real.log (500000000000 / 1068627450981) ≤ (3038089 / 4000000) := by
  have h := checkLog_sound (w := (68627450981 / 2068627450981)) (n := 12)
    (lo := (16593767 / 250000000)) (hi := (66375069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068627450981 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068627450981 / 1000000000000) = 1/(500000000000 / 1068627450981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (94940281 / 125000000) (3038089 / 4000000) (Real.log (1068627450981 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1068627450981 / 500000000000) = -Real.log (500000000000 / 1068627450981) := by
    rw [show ((1068627450981 / 500000000000) : ℝ) = ((500000000000 / 1068627450981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (526620273 / 1000000000) ≤ -Real.log (15625000000 / 26456251153) ∧
    -Real.log (15625000000 / 26456251153) ≤ (263310137 / 500000000) := by
  have h := checkLog_sound (w := (10831251153 / 42081251153)) (n := 12)
    (lo := (526620273 / 1000000000)) (hi := (263310137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26456251153 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26456251153 / 15625000000) = 1/(15625000000 / 26456251153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (526620273 / 1000000000) (263310137 / 500000000) (Real.log (26456251153 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (26456251153 / 15625000000) = -Real.log (15625000000 / 26456251153) := by
    rw [show ((26456251153 / 15625000000) : ℝ) = ((15625000000 / 26456251153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (263763201 / 500000000) ≤ -Real.log (500000000000 / 847367513353) ∧
    -Real.log (500000000000 / 847367513353) ≤ (527526403 / 1000000000) := by
  have h := checkLog_sound (w := (347367513353 / 1347367513353)) (n := 12)
    (lo := (263763201 / 500000000)) (hi := (527526403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847367513353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847367513353 / 500000000000) = 1/(500000000000 / 847367513353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (263763201 / 500000000) (527526403 / 1000000000) (Real.log (847367513353 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (847367513353 / 500000000000) = -Real.log (500000000000 / 847367513353) := by
    rw [show ((847367513353 / 500000000000) : ℝ) = ((500000000000 / 847367513353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (187573319 / 500000000) ≤ -Real.log (100000000000 / 145520478863) ∧
    -Real.log (100000000000 / 145520478863) ≤ (375146639 / 1000000000) := by
  have h := checkLog_sound (w := (45520478863 / 245520478863)) (n := 12)
    (lo := (187573319 / 500000000)) (hi := (375146639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145520478863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145520478863 / 100000000000) = 1/(100000000000 / 145520478863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (187573319 / 500000000) (375146639 / 1000000000) (Real.log (145520478863 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145520478863 / 100000000000) = -Real.log (100000000000 / 145520478863) := by
    rw [show ((145520478863 / 100000000000) : ℝ) = ((100000000000 / 145520478863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (46975147 / 125000000) ≤ -Real.log (7812500000 / 11376231149) ∧
    -Real.log (7812500000 / 11376231149) ≤ (375801177 / 1000000000) := by
  have h := checkLog_sound (w := (3563731149 / 19188731149)) (n := 12)
    (lo := (46975147 / 125000000)) (hi := (375801177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11376231149 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11376231149 / 7812500000) = 1/(7812500000 / 11376231149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (46975147 / 125000000) (375801177 / 1000000000) (Real.log (11376231149 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11376231149 / 7812500000) = -Real.log (7812500000 / 11376231149) := by
    rw [show ((11376231149 / 7812500000) : ℝ) = ((7812500000 / 11376231149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17550403 / 500000000) ≤ -Real.log (603442551 / 625000000) ∧
    -Real.log (603442551 / 625000000) ≤ (35100807 / 1000000000) := by
  have h := checkLog_sound (w := (21557449 / 1228442551)) (n := 12)
    (lo := (17550403 / 500000000)) (hi := (35100807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 603442551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 603442551) = 1/(603442551 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35100807 / 1000000000) (-17550403 / 500000000) (Real.log (603442551 / 625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34979349 / 1000000000) ≤ -Real.log (60351584799 / 62500000000) ∧
    -Real.log (60351584799 / 62500000000) ≤ (699587 / 20000000) := by
  have h := checkLog_sound (w := (2148415201 / 122851584799)) (n := 12)
    (lo := (34979349 / 1000000000)) (hi := (699587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60351584799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60351584799) = 1/(60351584799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-699587 / 20000000) (-34979349 / 1000000000) (Real.log (60351584799 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell192Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell192
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

theorem reflection_log_1_neg : (387189 / 1250000) ≤ -Real.log (5120 / 6979) ∧
    -Real.log (5120 / 6979) ≤ (309751201 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 12099)) (n := 12)
    (lo := (387189 / 1250000)) (hi := (309751201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6979 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6979 / 5120) = 1/(5120 / 6979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (387189 / 1250000) (309751201 / 1000000000) (Real.log (6979 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6979 / 5120) = -Real.log (5120 / 6979) := by
    rw [show ((6979 / 5120) : ℝ) = ((5120 / 6979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225560271 / 500000000) ≤ -Real.log (3261 / 5120) ∧
    -Real.log (3261 / 5120) ≤ (451120543 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 8381)) (n := 12)
    (lo := (225560271 / 500000000)) (hi := (451120543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3261) = 1/(3261 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-451120543 / 1000000000) (-225560271 / 500000000) (Real.log (3261 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (309321247 / 1000000000) ≤ -Real.log (80 / 109) ∧
    -Real.log (80 / 109) ≤ (9666289 / 31250000) := by
  have h := checkLog_sound (w := (29 / 189)) (n := 12)
    (lo := (309321247 / 1000000000)) (hi := (9666289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109 / 80) = 1/(80 / 109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (309321247 / 1000000000) (9666289 / 31250000) (Real.log (109 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (109 / 80) = -Real.log (80 / 109) := by
    rw [show ((109 / 80) : ℝ) = ((80 / 109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (450201001 / 1000000000) ≤ -Real.log (51 / 80) ∧
    -Real.log (51 / 80) ≤ (225100501 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 51) = 1/(51 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-225100501 / 500000000) (-450201001 / 1000000000) (Real.log (51 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (57343227 / 250000000) ≤ -Real.log (1000000 / 1257811) ∧
    -Real.log (1000000 / 1257811) ≤ (229372909 / 1000000000) := by
  have h := checkLog_sound (w := (257811 / 2257811)) (n := 12)
    (lo := (57343227 / 250000000)) (hi := (229372909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257811 / 1000000) = 1/(1000000 / 1257811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (57343227 / 250000000) (229372909 / 1000000000) (Real.log (1257811 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1257811 / 1000000) = -Real.log (1000000 / 1257811) := by
    rw [show ((1257811 / 1000000) : ℝ) = ((1000000 / 1257811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298151351 / 1000000000) ≤ -Real.log (742189 / 1000000) ∧
    -Real.log (742189 / 1000000) ≤ (37268919 / 125000000) := by
  have h := checkLog_sound (w := (257811 / 1742189)) (n := 12)
    (lo := (298151351 / 1000000000)) (hi := (37268919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742189) = 1/(742189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-37268919 / 125000000) (-298151351 / 1000000000) (Real.log (742189 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4594183 / 20000000) ≤ -Real.log (500000 / 629117) ∧
    -Real.log (500000 / 629117) ≤ (229709151 / 1000000000) := by
  have h := checkLog_sound (w := (129117 / 1129117)) (n := 12)
    (lo := (4594183 / 20000000)) (hi := (229709151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629117 / 500000) = 1/(500000 / 629117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4594183 / 20000000) (229709151 / 1000000000) (Real.log (629117 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629117 / 500000) = -Real.log (500000 / 629117) := by
    rw [show ((629117 / 500000) : ℝ) = ((500000 / 629117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298721449 / 1000000000) ≤ -Real.log (370883 / 500000) ∧
    -Real.log (370883 / 500000) ≤ (5974429 / 20000000) := by
  have h := checkLog_sound (w := (129117 / 870883)) (n := 12)
    (lo := (298721449 / 1000000000)) (hi := (5974429 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370883) = 1/(370883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5974429 / 20000000) (-298721449 / 1000000000) (Real.log (370883 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170349341 / 1000000000) ≤ -Real.log (1000000 / 1185719) ∧
    -Real.log (1000000 / 1185719) ≤ (85174671 / 500000000) := by
  have h := checkLog_sound (w := (185719 / 2185719)) (n := 12)
    (lo := (170349341 / 1000000000)) (hi := (85174671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185719 / 1000000) = 1/(1000000 / 1185719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170349341 / 1000000000) (85174671 / 500000000) (Real.log (1185719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1185719 / 1000000) = -Real.log (1000000 / 1185719) := by
    rw [show ((1185719 / 1000000) : ℝ) = ((1000000 / 1185719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205449763 / 1000000000) ≤ -Real.log (814281 / 1000000) ∧
    -Real.log (814281 / 1000000) ≤ (51362441 / 250000000) := by
  have h := checkLog_sound (w := (185719 / 1814281)) (n := 12)
    (lo := (205449763 / 1000000000)) (hi := (51362441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814281) = 1/(814281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-51362441 / 250000000) (-205449763 / 1000000000) (Real.log (814281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85308327 / 500000000) ≤ -Real.log (250000 / 296509) ∧
    -Real.log (250000 / 296509) ≤ (34123331 / 200000000) := by
  have h := checkLog_sound (w := (46509 / 546509)) (n := 12)
    (lo := (85308327 / 500000000)) (hi := (34123331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296509 / 250000) = 1/(250000 / 296509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85308327 / 500000000) (34123331 / 200000000) (Real.log (296509 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (296509 / 250000) = -Real.log (250000 / 296509) := by
    rw [show ((296509 / 250000) : ℝ) = ((250000 / 296509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10291957 / 50000000) ≤ -Real.log (203491 / 250000) ∧
    -Real.log (203491 / 250000) ≤ (205839141 / 1000000000) := by
  have h := checkLog_sound (w := (46509 / 453491)) (n := 12)
    (lo := (10291957 / 50000000)) (hi := (205839141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203491) = 1/(203491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-205839141 / 1000000000) (-10291957 / 50000000) (Real.log (203491 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94940281 / 125000000) ≤ -Real.log (25000000000 / 53431372549) ∧
    -Real.log (25000000000 / 53431372549) ≤ (3038089 / 4000000) := by
  have h := checkLog_sound (w := (3431372549 / 103431372549)) (n := 12)
    (lo := (16593767 / 250000000)) (hi := (66375069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53431372549 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53431372549 / 50000000000) = 1/(25000000000 / 53431372549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94940281 / 125000000) (3038089 / 4000000) (Real.log (53431372549 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53431372549 / 25000000000) = -Real.log (25000000000 / 53431372549) := by
    rw [show ((53431372549 / 25000000000) : ℝ) = ((25000000000 / 53431372549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (380435871 / 500000000) ≤ -Real.log (500000000000 / 1070070530513) ∧
    -Real.log (500000000000 / 1070070530513) ≤ (11888621 / 15625000) := by
  have h := checkLog_sound (w := (70070530513 / 2070070530513)) (n := 12)
    (lo := (33862281 / 500000000)) (hi := (67724563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070070530513 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070070530513 / 1000000000000) = 1/(500000000000 / 1070070530513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (380435871 / 500000000) (11888621 / 15625000) (Real.log (1070070530513 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1070070530513 / 500000000000) = -Real.log (500000000000 / 1070070530513) := by
    rw [show ((1070070530513 / 500000000000) : ℝ) = ((500000000000 / 1070070530513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (527524259 / 1000000000) ≤ -Real.log (100000000000 / 169473139591) ∧
    -Real.log (100000000000 / 169473139591) ≤ (26376213 / 50000000) := by
  have h := checkLog_sound (w := (69473139591 / 269473139591)) (n := 12)
    (lo := (527524259 / 1000000000)) (hi := (26376213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169473139591 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169473139591 / 100000000000) = 1/(100000000000 / 169473139591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (527524259 / 1000000000) (26376213 / 50000000) (Real.log (169473139591 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (169473139591 / 100000000000) = -Real.log (100000000000 / 169473139591) := by
    rw [show ((169473139591 / 100000000000) : ℝ) = ((100000000000 / 169473139591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (528430599 / 1000000000) ≤ -Real.log (100000000000 / 169626809533) ∧
    -Real.log (100000000000 / 169626809533) ≤ (2642153 / 5000000) := by
  have h := checkLog_sound (w := (69626809533 / 269626809533)) (n := 12)
    (lo := (528430599 / 1000000000)) (hi := (2642153 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169626809533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169626809533 / 100000000000) = 1/(100000000000 / 169626809533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (528430599 / 1000000000) (2642153 / 5000000) (Real.log (169626809533 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (169626809533 / 100000000000) = -Real.log (100000000000 / 169626809533) := by
    rw [show ((169626809533 / 100000000000) : ℝ) = ((100000000000 / 169626809533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (75159821 / 200000000) ≤ -Real.log (500000000000 / 728077285359) ∧
    -Real.log (500000000000 / 728077285359) ≤ (187899553 / 500000000) := by
  have h := checkLog_sound (w := (228077285359 / 1228077285359)) (n := 12)
    (lo := (75159821 / 200000000)) (hi := (187899553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728077285359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728077285359 / 500000000000) = 1/(500000000000 / 728077285359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (75159821 / 200000000) (187899553 / 500000000) (Real.log (728077285359 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (728077285359 / 500000000000) = -Real.log (500000000000 / 728077285359) := by
    rw [show ((728077285359 / 500000000000) : ℝ) = ((500000000000 / 728077285359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188227897 / 500000000) ≤ -Real.log (250000000000 / 364277781327) ∧
    -Real.log (250000000000 / 364277781327) ≤ (75291159 / 200000000) := by
  have h := checkLog_sound (w := (114277781327 / 614277781327)) (n := 12)
    (lo := (188227897 / 500000000)) (hi := (75291159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364277781327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364277781327 / 250000000000) = 1/(250000000000 / 364277781327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188227897 / 500000000) (75291159 / 200000000) (Real.log (364277781327 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (364277781327 / 250000000000) = -Real.log (250000000000 / 364277781327) := by
    rw [show ((364277781327 / 250000000000) : ℝ) = ((250000000000 / 364277781327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7044497 / 200000000) ≤ -Real.log (60336912919 / 62500000000) ∧
    -Real.log (60336912919 / 62500000000) ≤ (17611243 / 500000000) := by
  have h := checkLog_sound (w := (2163087081 / 122836912919)) (n := 12)
    (lo := (7044497 / 200000000)) (hi := (17611243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60336912919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60336912919) = 1/(60336912919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17611243 / 500000000) (-7044497 / 200000000) (Real.log (60336912919 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17550211 / 500000000) ≤ -Real.log (965508453039 / 1000000000000) ∧
    -Real.log (965508453039 / 1000000000000) ≤ (35100423 / 1000000000) := by
  have h := checkLog_sound (w := (34491546961 / 1965508453039)) (n := 12)
    (lo := (17550211 / 500000000)) (hi := (35100423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965508453039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965508453039) = 1/(965508453039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35100423 / 1000000000) (-17550211 / 500000000) (Real.log (965508453039 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell192

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell193Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell193
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

theorem reflection_log_1_neg : (310180969 / 1000000000) ≤ -Real.log (2560 / 3491) ∧
    -Real.log (2560 / 3491) ≤ (31018097 / 100000000) := by
  have h := checkLog_sound (w := (931 / 6051)) (n := 12)
    (lo := (310180969 / 1000000000)) (hi := (31018097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3491 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3491 / 2560) = 1/(2560 / 3491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310180969 / 1000000000) (31018097 / 100000000) (Real.log (3491 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3491 / 2560) = -Real.log (2560 / 3491) := by
    rw [show ((3491 / 2560) : ℝ) = ((2560 / 3491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14126279 / 31250000) ≤ -Real.log (1629 / 2560) ∧
    -Real.log (1629 / 2560) ≤ (452040929 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 4189)) (n := 12)
    (lo := (14126279 / 31250000)) (hi := (452040929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1629) = 1/(1629 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-452040929 / 1000000000) (-14126279 / 31250000) (Real.log (1629 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (387189 / 1250000) ≤ -Real.log (5120 / 6979) ∧
    -Real.log (5120 / 6979) ≤ (309751201 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 12099)) (n := 12)
    (lo := (387189 / 1250000)) (hi := (309751201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6979 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6979 / 5120) = 1/(5120 / 6979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (387189 / 1250000) (309751201 / 1000000000) (Real.log (6979 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6979 / 5120) = -Real.log (5120 / 6979) := by
    rw [show ((6979 / 5120) : ℝ) = ((5120 / 6979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225560271 / 500000000) ≤ -Real.log (3261 / 5120) ∧
    -Real.log (3261 / 5120) ≤ (451120543 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 8381)) (n := 12)
    (lo := (225560271 / 500000000)) (hi := (451120543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3261) = 1/(3261 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-451120543 / 1000000000) (-225560271 / 500000000) (Real.log (3261 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45941671 / 200000000) ≤ -Real.log (1000000 / 1258233) ∧
    -Real.log (1000000 / 1258233) ≤ (57427089 / 250000000) := by
  have h := checkLog_sound (w := (258233 / 2258233)) (n := 12)
    (lo := (45941671 / 200000000)) (hi := (57427089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258233 / 1000000) = 1/(1000000 / 1258233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45941671 / 200000000) (57427089 / 250000000) (Real.log (1258233 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1258233 / 1000000) = -Real.log (1000000 / 1258233) := by
    rw [show ((1258233 / 1000000) : ℝ) = ((1000000 / 1258233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298720101 / 1000000000) ≤ -Real.log (741767 / 1000000) ∧
    -Real.log (741767 / 1000000) ≤ (149360051 / 500000000) := by
  have h := checkLog_sound (w := (258233 / 1741767)) (n := 12)
    (lo := (298720101 / 1000000000)) (hi := (149360051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741767) = 1/(741767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149360051 / 500000000) (-298720101 / 1000000000) (Real.log (741767 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46008897 / 200000000) ≤ -Real.log (31250 / 39333) ∧
    -Real.log (31250 / 39333) ≤ (115022243 / 500000000) := by
  have h := checkLog_sound (w := (8083 / 70583)) (n := 12)
    (lo := (46008897 / 200000000)) (hi := (115022243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39333 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39333 / 31250) = 1/(31250 / 39333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46008897 / 200000000) (115022243 / 500000000) (Real.log (39333 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (39333 / 31250) = -Real.log (31250 / 39333) := by
    rw [show ((39333 / 31250) : ℝ) = ((31250 / 39333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (299290523 / 1000000000) ≤ -Real.log (23167 / 31250) ∧
    -Real.log (23167 / 31250) ≤ (74822631 / 250000000) := by
  have h := checkLog_sound (w := (8083 / 54417)) (n := 12)
    (lo := (299290523 / 1000000000)) (hi := (74822631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23167) = 1/(23167 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-74822631 / 250000000) (-299290523 / 1000000000) (Real.log (23167 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170615811 / 1000000000) ≤ -Real.log (200000 / 237207) ∧
    -Real.log (200000 / 237207) ≤ (42653953 / 250000000) := by
  have h := checkLog_sound (w := (37207 / 437207)) (n := 12)
    (lo := (170615811 / 1000000000)) (hi := (42653953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237207 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237207 / 200000) = 1/(200000 / 237207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170615811 / 1000000000) (42653953 / 250000000) (Real.log (237207 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (237207 / 200000) = -Real.log (200000 / 237207) := by
    rw [show ((237207 / 200000) : ℝ) = ((200000 / 237207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205837911 / 1000000000) ≤ -Real.log (162793 / 200000) ∧
    -Real.log (162793 / 200000) ≤ (25729739 / 125000000) := by
  have h := checkLog_sound (w := (37207 / 362793)) (n := 12)
    (lo := (205837911 / 1000000000)) (hi := (25729739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162793) = 1/(162793 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25729739 / 125000000) (-205837911 / 1000000000) (Real.log (162793 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170882209 / 1000000000) ≤ -Real.log (1000000 / 1186351) ∧
    -Real.log (1000000 / 1186351) ≤ (17088221 / 100000000) := by
  have h := checkLog_sound (w := (186351 / 2186351)) (n := 12)
    (lo := (170882209 / 1000000000)) (hi := (17088221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186351 / 1000000) = 1/(1000000 / 1186351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170882209 / 1000000000) (17088221 / 100000000) (Real.log (1186351 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1186351 / 1000000) = -Real.log (1000000 / 1186351) := by
    rw [show ((1186351 / 1000000) : ℝ) = ((1000000 / 1186351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (206226209 / 1000000000) ≤ -Real.log (813649 / 1000000) ∧
    -Real.log (813649 / 1000000) ≤ (20622621 / 100000000) := by
  have h := checkLog_sound (w := (186351 / 1813649)) (n := 12)
    (lo := (206226209 / 1000000000)) (hi := (20622621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813649) = 1/(813649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20622621 / 100000000) (-206226209 / 1000000000) (Real.log (813649 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (380435871 / 500000000) ≤ -Real.log (31250000000 / 66879408157) ∧
    -Real.log (31250000000 / 66879408157) ≤ (11888621 / 15625000) := by
  have h := checkLog_sound (w := (4379408157 / 129379408157)) (n := 12)
    (lo := (33862281 / 500000000)) (hi := (67724563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66879408157 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66879408157 / 62500000000) = 1/(31250000000 / 66879408157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (380435871 / 500000000) (11888621 / 15625000) (Real.log (66879408157 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66879408157 / 31250000000) = -Real.log (31250000000 / 66879408157) := by
    rw [show ((66879408157 / 31250000000) : ℝ) = ((31250000000 / 66879408157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (762221897 / 1000000000) ≤ -Real.log (500000000000 / 1071516267649) ∧
    -Real.log (500000000000 / 1071516267649) ≤ (762221899 / 1000000000) := by
  have h := checkLog_sound (w := (71516267649 / 2071516267649)) (n := 12)
    (lo := (69074717 / 1000000000)) (hi := (34537359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1071516267649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1071516267649 / 1000000000000) = 1/(500000000000 / 1071516267649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (762221897 / 1000000000) (762221899 / 1000000000) (Real.log (1071516267649 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1071516267649 / 500000000000) = -Real.log (500000000000 / 1071516267649) := by
    rw [show ((1071516267649 / 500000000000) : ℝ) = ((500000000000 / 1071516267649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (528428457 / 1000000000) ≤ -Real.log (500000000000 / 848132230201) ∧
    -Real.log (500000000000 / 848132230201) ≤ (264214229 / 500000000) := by
  have h := checkLog_sound (w := (348132230201 / 1348132230201)) (n := 12)
    (lo := (528428457 / 1000000000)) (hi := (264214229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848132230201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848132230201 / 500000000000) = 1/(500000000000 / 848132230201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (528428457 / 1000000000) (264214229 / 500000000) (Real.log (848132230201 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (848132230201 / 500000000000) = -Real.log (500000000000 / 848132230201) := by
    rw [show ((848132230201 / 500000000000) : ℝ) = ((500000000000 / 848132230201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16541719 / 31250000) ≤ -Real.log (7812500000 / 13264085229) ∧
    -Real.log (7812500000 / 13264085229) ≤ (529335009 / 1000000000) := by
  have h := checkLog_sound (w := (5451585229 / 21076585229)) (n := 12)
    (lo := (16541719 / 31250000)) (hi := (529335009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13264085229 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13264085229 / 7812500000) = 1/(7812500000 / 13264085229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (16541719 / 31250000) (529335009 / 1000000000) (Real.log (13264085229 / 7812500000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (13264085229 / 7812500000) = -Real.log (7812500000 / 13264085229) := by
    rw [show ((13264085229 / 7812500000) : ℝ) = ((7812500000 / 13264085229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (188226861 / 500000000) ≤ -Real.log (250000000000 / 364277026653) ∧
    -Real.log (250000000000 / 364277026653) ≤ (376453723 / 1000000000) := by
  have h := checkLog_sound (w := (114277026653 / 614277026653)) (n := 12)
    (lo := (188226861 / 500000000)) (hi := (376453723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364277026653 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364277026653 / 250000000000) = 1/(250000000000 / 364277026653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188226861 / 500000000) (376453723 / 1000000000) (Real.log (364277026653 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (364277026653 / 250000000000) = -Real.log (250000000000 / 364277026653) := by
    rw [show ((364277026653 / 250000000000) : ℝ) = ((250000000000 / 364277026653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (377108419 / 1000000000) ≤ -Real.log (500000000000 / 729031191583) ∧
    -Real.log (500000000000 / 729031191583) ≤ (18855421 / 50000000) := by
  have h := checkLog_sound (w := (229031191583 / 1229031191583)) (n := 12)
    (lo := (377108419 / 1000000000)) (hi := (18855421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729031191583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729031191583 / 500000000000) = 1/(500000000000 / 729031191583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (377108419 / 1000000000) (18855421 / 50000000) (Real.log (729031191583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (729031191583 / 500000000000) = -Real.log (500000000000 / 729031191583) := by
    rw [show ((729031191583 / 500000000000) : ℝ) = ((500000000000 / 729031191583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2209 / 62500) ≤ -Real.log (965273304799 / 1000000000000) ∧
    -Real.log (965273304799 / 1000000000000) ≤ (35344001 / 1000000000) := by
  have h := checkLog_sound (w := (34726695201 / 1965273304799)) (n := 12)
    (lo := (2209 / 62500)) (hi := (35344001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965273304799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965273304799) = 1/(965273304799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35344001 / 1000000000) (-2209 / 62500) (Real.log (965273304799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (352221 / 10000000) ≤ -Real.log (38615639151 / 40000000000) ∧
    -Real.log (38615639151 / 40000000000) ≤ (35222101 / 1000000000) := by
  have h := checkLog_sound (w := (1384360849 / 78615639151)) (n := 12)
    (lo := (352221 / 10000000)) (hi := (35222101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38615639151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38615639151) = 1/(38615639151 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35222101 / 1000000000) (-352221 / 10000000) (Real.log (38615639151 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell193

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell194Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell194
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

theorem reflection_log_1_neg : (310610553 / 1000000000) ≤ -Real.log (1024 / 1397) ∧
    -Real.log (1024 / 1397) ≤ (155305277 / 500000000) := by
  have h := checkLog_sound (w := (373 / 2421)) (n := 12)
    (lo := (310610553 / 1000000000)) (hi := (155305277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1024) = 1/(1024 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310610553 / 1000000000) (155305277 / 500000000) (Real.log (1397 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1397 / 1024) = -Real.log (1024 / 1397) := by
    rw [show ((1397 / 1024) : ℝ) = ((1024 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (452962163 / 1000000000) ≤ -Real.log (651 / 1024) ∧
    -Real.log (651 / 1024) ≤ (113240541 / 250000000) := by
  have h := checkLog_sound (w := (373 / 1675)) (n := 12)
    (lo := (452962163 / 1000000000)) (hi := (113240541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 651) = 1/(651 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113240541 / 250000000) (-452962163 / 1000000000) (Real.log (651 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310180969 / 1000000000) ≤ -Real.log (2560 / 3491) ∧
    -Real.log (2560 / 3491) ≤ (31018097 / 100000000) := by
  have h := checkLog_sound (w := (931 / 6051)) (n := 12)
    (lo := (310180969 / 1000000000)) (hi := (31018097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3491 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3491 / 2560) = 1/(2560 / 3491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310180969 / 1000000000) (31018097 / 100000000) (Real.log (3491 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3491 / 2560) = -Real.log (2560 / 3491) := by
    rw [show ((3491 / 2560) : ℝ) = ((2560 / 3491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14126279 / 31250000) ≤ -Real.log (1629 / 2560) ∧
    -Real.log (1629 / 2560) ≤ (452040929 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 4189)) (n := 12)
    (lo := (14126279 / 31250000)) (hi := (452040929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1629) = 1/(1629 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-452040929 / 1000000000) (-14126279 / 31250000) (Real.log (1629 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23004369 / 100000000) ≤ -Real.log (200000 / 251731) ∧
    -Real.log (200000 / 251731) ≤ (230043691 / 1000000000) := by
  have h := checkLog_sound (w := (51731 / 451731)) (n := 12)
    (lo := (23004369 / 100000000)) (hi := (230043691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251731 / 200000) = 1/(200000 / 251731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23004369 / 100000000) (230043691 / 1000000000) (Real.log (251731 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (251731 / 200000) = -Real.log (200000 / 251731) := by
    rw [show ((251731 / 200000) : ℝ) = ((200000 / 251731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (149644587 / 500000000) ≤ -Real.log (148269 / 200000) ∧
    -Real.log (148269 / 200000) ≤ (11971567 / 40000000) := by
  have h := checkLog_sound (w := (51731 / 348269)) (n := 12)
    (lo := (149644587 / 500000000)) (hi := (11971567 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148269) = 1/(148269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11971567 / 40000000) (-149644587 / 500000000) (Real.log (148269 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (230379707 / 1000000000) ≤ -Real.log (500000 / 629539) ∧
    -Real.log (500000 / 629539) ≤ (57594927 / 250000000) := by
  have h := checkLog_sound (w := (129539 / 1129539)) (n := 12)
    (lo := (230379707 / 1000000000)) (hi := (57594927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629539 / 500000) = 1/(500000 / 629539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (230379707 / 1000000000) (57594927 / 250000000) (Real.log (629539 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629539 / 500000) = -Real.log (500000 / 629539) := by
    rw [show ((629539 / 500000) : ℝ) = ((500000 / 629539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (149929961 / 500000000) ≤ -Real.log (370461 / 500000) ∧
    -Real.log (370461 / 500000) ≤ (299859923 / 1000000000) := by
  have h := checkLog_sound (w := (129539 / 870461)) (n := 12)
    (lo := (149929961 / 500000000)) (hi := (299859923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370461) = 1/(370461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-299859923 / 1000000000) (-149929961 / 500000000) (Real.log (370461 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85440683 / 500000000) ≤ -Real.log (20000 / 23727) ∧
    -Real.log (20000 / 23727) ≤ (170881367 / 1000000000) := by
  have h := checkLog_sound (w := (3727 / 43727)) (n := 12)
    (lo := (85440683 / 500000000)) (hi := (170881367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23727 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23727 / 20000) = 1/(20000 / 23727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85440683 / 500000000) (170881367 / 1000000000) (Real.log (23727 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23727 / 20000) = -Real.log (20000 / 23727) := by
    rw [show ((23727 / 20000) : ℝ) = ((20000 / 23727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10311249 / 50000000) ≤ -Real.log (16273 / 20000) ∧
    -Real.log (16273 / 20000) ≤ (206224981 / 1000000000) := by
  have h := checkLog_sound (w := (3727 / 36273)) (n := 12)
    (lo := (10311249 / 50000000)) (hi := (206224981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16273) = 1/(16273 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-206224981 / 1000000000) (-10311249 / 50000000) (Real.log (16273 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171148537 / 1000000000) ≤ -Real.log (1000000 / 1186667) ∧
    -Real.log (1000000 / 1186667) ≤ (85574269 / 500000000) := by
  have h := checkLog_sound (w := (186667 / 2186667)) (n := 12)
    (lo := (171148537 / 1000000000)) (hi := (85574269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186667 / 1000000) = 1/(1000000 / 1186667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171148537 / 1000000000) (85574269 / 500000000) (Real.log (1186667 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1186667 / 1000000) = -Real.log (1000000 / 1186667) := by
    rw [show ((1186667 / 1000000) : ℝ) = ((1000000 / 1186667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (206614659 / 1000000000) ≤ -Real.log (813333 / 1000000) ∧
    -Real.log (813333 / 1000000) ≤ (10330733 / 50000000) := by
  have h := checkLog_sound (w := (186667 / 1813333)) (n := 12)
    (lo := (206614659 / 1000000000)) (hi := (10330733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813333) = 1/(813333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10330733 / 50000000) (-206614659 / 1000000000) (Real.log (813333 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (762221897 / 1000000000) ≤ -Real.log (3906250000 / 8371220841) ∧
    -Real.log (3906250000 / 8371220841) ≤ (762221899 / 1000000000) := by
  have h := checkLog_sound (w := (558720841 / 16183720841)) (n := 12)
    (lo := (69074717 / 1000000000)) (hi := (34537359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8371220841 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8371220841 / 7812500000) = 1/(3906250000 / 8371220841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (762221897 / 1000000000) (762221899 / 1000000000) (Real.log (8371220841 / 3906250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8371220841 / 3906250000) = -Real.log (3906250000 / 8371220841) := by
    rw [show ((8371220841 / 3906250000) : ℝ) = ((3906250000 / 8371220841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (190893179 / 250000000) ≤ -Real.log (500000000000 / 1072964669739) ∧
    -Real.log (500000000000 / 1072964669739) ≤ (381786359 / 500000000) := by
  have h := checkLog_sound (w := (72964669739 / 2072964669739)) (n := 12)
    (lo := (1100399 / 15625000)) (hi := (70425537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1072964669739 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1072964669739 / 1000000000000) = 1/(500000000000 / 1072964669739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (190893179 / 250000000) (381786359 / 500000000) (Real.log (1072964669739 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1072964669739 / 500000000000) = -Real.log (500000000000 / 1072964669739) := by
    rw [show ((1072964669739 / 500000000000) : ℝ) = ((500000000000 / 1072964669739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (105866573 / 200000000) ≤ -Real.log (250000000000 / 424449817561) ∧
    -Real.log (250000000000 / 424449817561) ≤ (264666433 / 500000000) := by
  have h := checkLog_sound (w := (174449817561 / 674449817561)) (n := 12)
    (lo := (105866573 / 200000000)) (hi := (264666433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424449817561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424449817561 / 250000000000) = 1/(250000000000 / 424449817561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105866573 / 200000000) (264666433 / 500000000) (Real.log (424449817561 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (424449817561 / 250000000000) = -Real.log (250000000000 / 424449817561) := by
    rw [show ((424449817561 / 250000000000) : ℝ) = ((250000000000 / 424449817561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (530239629 / 1000000000) ≤ -Real.log (62500000000 / 106208716977) ∧
    -Real.log (62500000000 / 106208716977) ≤ (53023963 / 100000000) := by
  have h := checkLog_sound (w := (43708716977 / 168708716977)) (n := 12)
    (lo := (530239629 / 1000000000)) (hi := (53023963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106208716977 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106208716977 / 62500000000) = 1/(62500000000 / 106208716977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (530239629 / 1000000000) (53023963 / 100000000) (Real.log (106208716977 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (106208716977 / 62500000000) = -Real.log (62500000000 / 106208716977) := by
    rw [show ((106208716977 / 62500000000) : ℝ) = ((62500000000 / 106208716977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (377106347 / 1000000000) ≤ -Real.log (250000000000 / 364514840533) ∧
    -Real.log (250000000000 / 364514840533) ≤ (94276587 / 250000000) := by
  have h := checkLog_sound (w := (114514840533 / 614514840533)) (n := 12)
    (lo := (377106347 / 1000000000)) (hi := (94276587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364514840533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364514840533 / 250000000000) = 1/(250000000000 / 364514840533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (377106347 / 1000000000) (94276587 / 250000000) (Real.log (364514840533 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (364514840533 / 250000000000) = -Real.log (250000000000 / 364514840533) := by
    rw [show ((364514840533 / 250000000000) : ℝ) = ((250000000000 / 364514840533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (94440799 / 250000000) ≤ -Real.log (500000000000 / 729508700619) ∧
    -Real.log (500000000000 / 729508700619) ≤ (377763197 / 1000000000) := by
  have h := checkLog_sound (w := (229508700619 / 1229508700619)) (n := 12)
    (lo := (94440799 / 250000000)) (hi := (377763197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729508700619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729508700619 / 500000000000) = 1/(500000000000 / 729508700619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (94440799 / 250000000) (377763197 / 1000000000) (Real.log (729508700619 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (729508700619 / 500000000000) = -Real.log (500000000000 / 729508700619) := by
    rw [show ((729508700619 / 500000000000) : ℝ) = ((500000000000 / 729508700619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17733061 / 500000000) ≤ -Real.log (965155431111 / 1000000000000) ∧
    -Real.log (965155431111 / 1000000000000) ≤ (35466123 / 1000000000) := by
  have h := checkLog_sound (w := (34844568889 / 1965155431111)) (n := 12)
    (lo := (17733061 / 500000000)) (hi := (35466123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965155431111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965155431111) = 1/(965155431111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35466123 / 1000000000) (-17733061 / 500000000) (Real.log (965155431111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17671807 / 500000000) ≤ -Real.log (386109471 / 400000000) ∧
    -Real.log (386109471 / 400000000) ≤ (7068723 / 200000000) := by
  have h := checkLog_sound (w := (13890529 / 786109471)) (n := 12)
    (lo := (17671807 / 500000000)) (hi := (7068723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 386109471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 386109471) = 1/(386109471 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7068723 / 200000000) (-17671807 / 500000000) (Real.log (386109471 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell194

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell195Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell195
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

theorem reflection_log_1_neg : (311039953 / 1000000000) ≤ -Real.log (1280 / 1747) ∧
    -Real.log (1280 / 1747) ≤ (155519977 / 500000000) := by
  have h := checkLog_sound (w := (467 / 3027)) (n := 12)
    (lo := (311039953 / 1000000000)) (hi := (155519977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1747 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1747 / 1280) = 1/(1280 / 1747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311039953 / 1000000000) (155519977 / 500000000) (Real.log (1747 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1747 / 1280) = -Real.log (1280 / 1747) := by
    rw [show ((1747 / 1280) : ℝ) = ((1280 / 1747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (453884247 / 1000000000) ≤ -Real.log (813 / 1280) ∧
    -Real.log (813 / 1280) ≤ (56735531 / 125000000) := by
  have h := checkLog_sound (w := (467 / 2093)) (n := 12)
    (lo := (453884247 / 1000000000)) (hi := (56735531 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 813) = 1/(813 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-56735531 / 125000000) (-453884247 / 1000000000) (Real.log (813 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310610553 / 1000000000) ≤ -Real.log (1024 / 1397) ∧
    -Real.log (1024 / 1397) ≤ (155305277 / 500000000) := by
  have h := checkLog_sound (w := (373 / 2421)) (n := 12)
    (lo := (310610553 / 1000000000)) (hi := (155305277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1024) = 1/(1024 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310610553 / 1000000000) (155305277 / 500000000) (Real.log (1397 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1397 / 1024) = -Real.log (1024 / 1397) := by
    rw [show ((1397 / 1024) : ℝ) = ((1024 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (452962163 / 1000000000) ≤ -Real.log (651 / 1024) ∧
    -Real.log (651 / 1024) ≤ (113240541 / 250000000) := by
  have h := checkLog_sound (w := (373 / 1675)) (n := 12)
    (lo := (452962163 / 1000000000)) (hi := (113240541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 651) = 1/(651 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113240541 / 250000000) (-452962163 / 1000000000) (Real.log (651 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7199341 / 31250000) ≤ -Real.log (1000000 / 1259077) ∧
    -Real.log (1000000 / 1259077) ≤ (230378913 / 1000000000) := by
  have h := checkLog_sound (w := (259077 / 2259077)) (n := 12)
    (lo := (7199341 / 31250000)) (hi := (230378913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259077 / 1000000) = 1/(1000000 / 1259077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7199341 / 31250000) (230378913 / 1000000000) (Real.log (1259077 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259077 / 1000000) = -Real.log (1000000 / 1259077) := by
    rw [show ((1259077 / 1000000) : ℝ) = ((1000000 / 1259077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74964643 / 250000000) ≤ -Real.log (740923 / 1000000) ∧
    -Real.log (740923 / 1000000) ≤ (299858573 / 1000000000) := by
  have h := checkLog_sound (w := (259077 / 1740923)) (n := 12)
    (lo := (74964643 / 250000000)) (hi := (299858573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740923) = 1/(740923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-299858573 / 1000000000) (-74964643 / 250000000) (Real.log (740923 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3604919 / 15625000) ≤ -Real.log (2000 / 2519) ∧
    -Real.log (2000 / 2519) ≤ (230714817 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4519)) (n := 12)
    (lo := (3604919 / 15625000)) (hi := (230714817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2519 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2519 / 2000) = 1/(2000 / 2519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3604919 / 15625000) (230714817 / 1000000000) (Real.log (2519 / 2000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2519 / 2000) = -Real.log (2000 / 2519) := by
    rw [show ((2519 / 2000) : ℝ) = ((2000 / 2519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60085929 / 200000000) ≤ -Real.log (1481 / 2000) ∧
    -Real.log (1481 / 2000) ≤ (150214823 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3481)) (n := 12)
    (lo := (60085929 / 200000000)) (hi := (150214823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1481) = 1/(1481 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-150214823 / 500000000) (-60085929 / 200000000) (Real.log (1481 / 2000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85573847 / 500000000) ≤ -Real.log (500000 / 593333) ∧
    -Real.log (500000 / 593333) ≤ (34229539 / 200000000) := by
  have h := checkLog_sound (w := (93333 / 1093333)) (n := 12)
    (lo := (85573847 / 500000000)) (hi := (34229539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593333 / 500000) = 1/(500000 / 593333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85573847 / 500000000) (34229539 / 200000000) (Real.log (593333 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (593333 / 500000) = -Real.log (500000 / 593333) := by
    rw [show ((593333 / 500000) : ℝ) = ((500000 / 593333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (206613429 / 1000000000) ≤ -Real.log (406667 / 500000) ∧
    -Real.log (406667 / 500000) ≤ (20661343 / 100000000) := by
  have h := checkLog_sound (w := (93333 / 906667)) (n := 12)
    (lo := (206613429 / 1000000000)) (hi := (20661343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406667) = 1/(406667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-20661343 / 100000000) (-206613429 / 1000000000) (Real.log (406667 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171413951 / 1000000000) ≤ -Real.log (500000 / 593491) ∧
    -Real.log (500000 / 593491) ≤ (2678343 / 15625000) := by
  have h := checkLog_sound (w := (93491 / 1093491)) (n := 12)
    (lo := (171413951 / 1000000000)) (hi := (2678343 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593491 / 500000) = 1/(500000 / 593491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171413951 / 1000000000) (2678343 / 15625000) (Real.log (593491 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (593491 / 500000) = -Real.log (500000 / 593491) := by
    rw [show ((593491 / 500000) : ℝ) = ((500000 / 593491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207002029 / 1000000000) ≤ -Real.log (406509 / 500000) ∧
    -Real.log (406509 / 500000) ≤ (20700203 / 100000000) := by
  have h := checkLog_sound (w := (93491 / 906509)) (n := 12)
    (lo := (207002029 / 1000000000)) (hi := (20700203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406509) = 1/(406509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20700203 / 100000000) (-207002029 / 1000000000) (Real.log (406509 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190893179 / 250000000) ≤ -Real.log (250000000000 / 536482334869) ∧
    -Real.log (250000000000 / 536482334869) ≤ (381786359 / 500000000) := by
  have h := checkLog_sound (w := (36482334869 / 1036482334869)) (n := 12)
    (lo := (1100399 / 15625000)) (hi := (70425537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536482334869 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(536482334869 / 500000000000) = 1/(250000000000 / 536482334869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190893179 / 250000000) (381786359 / 500000000) (Real.log (536482334869 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (536482334869 / 250000000000) = -Real.log (250000000000 / 536482334869) := by
    rw [show ((536482334869 / 250000000000) : ℝ) = ((250000000000 / 536482334869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3824621 / 5000000) ≤ -Real.log (250000000000 / 537207872079) ∧
    -Real.log (250000000000 / 537207872079) ≤ (382462101 / 500000000) := by
  have h := checkLog_sound (w := (37207872079 / 1037207872079)) (n := 12)
    (lo := (3588851 / 50000000)) (hi := (71777021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537207872079 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537207872079 / 500000000000) = 1/(250000000000 / 537207872079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (3824621 / 5000000) (382462101 / 500000000) (Real.log (537207872079 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (537207872079 / 250000000000) = -Real.log (250000000000 / 537207872079) := by
    rw [show ((537207872079 / 250000000000) : ℝ) = ((250000000000 / 537207872079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106047497 / 200000000) ≤ -Real.log (500000000000 / 849667914209) ∧
    -Real.log (500000000000 / 849667914209) ≤ (265118743 / 500000000) := by
  have h := checkLog_sound (w := (349667914209 / 1349667914209)) (n := 12)
    (lo := (106047497 / 200000000)) (hi := (265118743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849667914209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849667914209 / 500000000000) = 1/(500000000000 / 849667914209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106047497 / 200000000) (265118743 / 500000000) (Real.log (849667914209 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (849667914209 / 500000000000) = -Real.log (500000000000 / 849667914209) := by
    rw [show ((849667914209 / 500000000000) : ℝ) = ((500000000000 / 849667914209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (265572231 / 500000000) ≤ -Real.log (500000000000 / 850438892641) ∧
    -Real.log (500000000000 / 850438892641) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (350438892641 / 1350438892641)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850438892641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850438892641 / 500000000000) = 1/(500000000000 / 850438892641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (850438892641 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (850438892641 / 500000000000) = -Real.log (500000000000 / 850438892641) := by
    rw [show ((850438892641 / 500000000000) : ℝ) = ((500000000000 / 850438892641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94440281 / 250000000) ≤ -Real.log (7812500000 / 11398549827) ∧
    -Real.log (7812500000 / 11398549827) ≤ (3022089 / 8000000) := by
  have h := checkLog_sound (w := (3586049827 / 19211049827)) (n := 12)
    (lo := (94440281 / 250000000)) (hi := (3022089 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11398549827 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11398549827 / 7812500000) = 1/(7812500000 / 11398549827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94440281 / 250000000) (3022089 / 8000000) (Real.log (11398549827 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11398549827 / 7812500000) = -Real.log (7812500000 / 11398549827) := by
    rw [show ((11398549827 / 7812500000) : ℝ) = ((7812500000 / 11398549827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18920799 / 50000000) ≤ -Real.log (250000000000 / 364992533991) ∧
    -Real.log (250000000000 / 364992533991) ≤ (378415981 / 1000000000) := by
  have h := checkLog_sound (w := (114992533991 / 614992533991)) (n := 12)
    (lo := (18920799 / 50000000)) (hi := (378415981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364992533991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364992533991 / 250000000000) = 1/(250000000000 / 364992533991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18920799 / 50000000) (378415981 / 1000000000) (Real.log (364992533991 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (364992533991 / 250000000000) = -Real.log (250000000000 / 364992533991) := by
    rw [show ((364992533991 / 250000000000) : ℝ) = ((250000000000 / 364992533991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17794039 / 500000000) ≤ -Real.log (241259432919 / 250000000000) ∧
    -Real.log (241259432919 / 250000000000) ≤ (35588079 / 1000000000) := by
  have h := checkLog_sound (w := (8740567081 / 491259432919)) (n := 12)
    (lo := (17794039 / 500000000)) (hi := (35588079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241259432919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241259432919) = 1/(241259432919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35588079 / 1000000000) (-17794039 / 500000000) (Real.log (241259432919 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7093147 / 200000000) ≤ -Real.log (241288951111 / 250000000000) ∧
    -Real.log (241288951111 / 250000000000) ≤ (4433217 / 125000000) := by
  have h := checkLog_sound (w := (8711048889 / 491288951111)) (n := 12)
    (lo := (7093147 / 200000000)) (hi := (4433217 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241288951111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241288951111) = 1/(241288951111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4433217 / 125000000) (-7093147 / 200000000) (Real.log (241288951111 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell195

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell196Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell196
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

theorem reflection_log_1_neg : (19466823 / 62500000) ≤ -Real.log (5120 / 6991) ∧
    -Real.log (5120 / 6991) ≤ (311469169 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 12111)) (n := 12)
    (lo := (19466823 / 62500000)) (hi := (311469169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6991 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6991 / 5120) = 1/(5120 / 6991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19466823 / 62500000) (311469169 / 1000000000) (Real.log (6991 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6991 / 5120) = -Real.log (5120 / 6991) := by
    rw [show ((6991 / 5120) : ℝ) = ((5120 / 6991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227403591 / 500000000) ≤ -Real.log (3249 / 5120) ∧
    -Real.log (3249 / 5120) ≤ (454807183 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 8369)) (n := 12)
    (lo := (227403591 / 500000000)) (hi := (454807183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3249) = 1/(3249 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-454807183 / 1000000000) (-227403591 / 500000000) (Real.log (3249 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311039953 / 1000000000) ≤ -Real.log (1280 / 1747) ∧
    -Real.log (1280 / 1747) ≤ (155519977 / 500000000) := by
  have h := checkLog_sound (w := (467 / 3027)) (n := 12)
    (lo := (311039953 / 1000000000)) (hi := (155519977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1747 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1747 / 1280) = 1/(1280 / 1747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311039953 / 1000000000) (155519977 / 500000000) (Real.log (1747 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1747 / 1280) = -Real.log (1280 / 1747) := by
    rw [show ((1747 / 1280) : ℝ) = ((1280 / 1747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (453884247 / 1000000000) ≤ -Real.log (813 / 1280) ∧
    -Real.log (813 / 1280) ≤ (56735531 / 125000000) := by
  have h := checkLog_sound (w := (467 / 2093)) (n := 12)
    (lo := (453884247 / 1000000000)) (hi := (56735531 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 813) = 1/(813 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-56735531 / 125000000) (-453884247 / 1000000000) (Real.log (813 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115357011 / 500000000) ≤ -Real.log (1000000 / 1259499) ∧
    -Real.log (1000000 / 1259499) ≤ (230714023 / 1000000000) := by
  have h := checkLog_sound (w := (259499 / 2259499)) (n := 12)
    (lo := (115357011 / 500000000)) (hi := (230714023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259499 / 1000000) = 1/(1000000 / 1259499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115357011 / 500000000) (230714023 / 1000000000) (Real.log (1259499 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259499 / 1000000) = -Real.log (1000000 / 1259499) := by
    rw [show ((1259499 / 1000000) : ℝ) = ((1000000 / 1259499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150214147 / 500000000) ≤ -Real.log (740501 / 1000000) ∧
    -Real.log (740501 / 1000000) ≤ (60085659 / 200000000) := by
  have h := checkLog_sound (w := (259499 / 1740501)) (n := 12)
    (lo := (150214147 / 500000000)) (hi := (60085659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740501) = 1/(740501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60085659 / 200000000) (-150214147 / 500000000) (Real.log (740501 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (115524907 / 500000000) ≤ -Real.log (500000 / 629961) ∧
    -Real.log (500000 / 629961) ≤ (46209963 / 200000000) := by
  have h := checkLog_sound (w := (129961 / 1129961)) (n := 12)
    (lo := (115524907 / 500000000)) (hi := (46209963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629961 / 500000) = 1/(500000 / 629961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (115524907 / 500000000) (46209963 / 200000000) (Real.log (629961 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629961 / 500000) = -Real.log (500000 / 629961) := by
    rw [show ((629961 / 500000) : ℝ) = ((500000 / 629961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75249923 / 250000000) ≤ -Real.log (370039 / 500000) ∧
    -Real.log (370039 / 500000) ≤ (300999693 / 1000000000) := by
  have h := checkLog_sound (w := (129961 / 870039)) (n := 12)
    (lo := (75249923 / 250000000)) (hi := (300999693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370039) = 1/(370039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-300999693 / 1000000000) (-75249923 / 250000000) (Real.log (370039 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42853277 / 250000000) ≤ -Real.log (1000000 / 1186981) ∧
    -Real.log (1000000 / 1186981) ≤ (171413109 / 1000000000) := by
  have h := checkLog_sound (w := (186981 / 2186981)) (n := 12)
    (lo := (42853277 / 250000000)) (hi := (171413109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186981 / 1000000) = 1/(1000000 / 1186981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42853277 / 250000000) (171413109 / 1000000000) (Real.log (1186981 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1186981 / 1000000) = -Real.log (1000000 / 1186981) := by
    rw [show ((1186981 / 1000000) : ℝ) = ((1000000 / 1186981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207000799 / 1000000000) ≤ -Real.log (813019 / 1000000) ∧
    -Real.log (813019 / 1000000) ≤ (258751 / 1250000) := by
  have h := checkLog_sound (w := (186981 / 1813019)) (n := 12)
    (lo := (207000799 / 1000000000)) (hi := (258751 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813019) = 1/(813019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-258751 / 1250000) (-207000799 / 1000000000) (Real.log (813019 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171680137 / 1000000000) ≤ -Real.log (500000 / 593649) ∧
    -Real.log (500000 / 593649) ≤ (85840069 / 500000000) := by
  have h := checkLog_sound (w := (93649 / 1093649)) (n := 12)
    (lo := (171680137 / 1000000000)) (hi := (85840069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593649 / 500000) = 1/(500000 / 593649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171680137 / 1000000000) (85840069 / 500000000) (Real.log (593649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (593649 / 500000) = -Real.log (500000 / 593649) := by
    rw [show ((593649 / 500000) : ℝ) = ((500000 / 593649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10369539 / 50000000) ≤ -Real.log (406351 / 500000) ∧
    -Real.log (406351 / 500000) ≤ (207390781 / 1000000000) := by
  have h := checkLog_sound (w := (93649 / 906351)) (n := 12)
    (lo := (10369539 / 50000000)) (hi := (207390781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406351) = 1/(406351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-207390781 / 1000000000) (-10369539 / 50000000) (Real.log (406351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (3824621 / 5000000) ≤ -Real.log (500000000000 / 1074415744157) ∧
    -Real.log (500000000000 / 1074415744157) ≤ (382462101 / 500000000) := by
  have h := checkLog_sound (w := (74415744157 / 2074415744157)) (n := 12)
    (lo := (3588851 / 50000000)) (hi := (71777021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074415744157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074415744157 / 1000000000000) = 1/(500000000000 / 1074415744157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (3824621 / 5000000) (382462101 / 500000000) (Real.log (1074415744157 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1074415744157 / 500000000000) = -Real.log (500000000000 / 1074415744157) := by
    rw [show ((1074415744157 / 500000000000) : ℝ) = ((500000000000 / 1074415744157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15325527 / 20000000) ≤ -Real.log (125000000000 / 268967374577) ∧
    -Real.log (125000000000 / 268967374577) ≤ (2993267 / 3906250) := by
  have h := checkLog_sound (w := (18967374577 / 518967374577)) (n := 12)
    (lo := (7312917 / 100000000)) (hi := (73129171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268967374577 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(268967374577 / 250000000000) = 1/(125000000000 / 268967374577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (15325527 / 20000000) (2993267 / 3906250) (Real.log (268967374577 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (268967374577 / 125000000000) = -Real.log (125000000000 / 268967374577) := by
    rw [show ((268967374577 / 125000000000) : ℝ) = ((125000000000 / 268967374577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (531142317 / 1000000000) ≤ -Real.log (500000000000 / 850437068957) ∧
    -Real.log (500000000000 / 850437068957) ≤ (265571159 / 500000000) := by
  have h := checkLog_sound (w := (350437068957 / 1350437068957)) (n := 12)
    (lo := (531142317 / 1000000000)) (hi := (265571159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850437068957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850437068957 / 500000000000) = 1/(500000000000 / 850437068957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (531142317 / 1000000000) (265571159 / 500000000) (Real.log (850437068957 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (850437068957 / 500000000000) = -Real.log (500000000000 / 850437068957) := by
    rw [show ((850437068957 / 500000000000) : ℝ) = ((500000000000 / 850437068957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (532049507 / 1000000000) ≤ -Real.log (500000000000 / 851208926627) ∧
    -Real.log (500000000000 / 851208926627) ≤ (133012377 / 250000000) := by
  have h := checkLog_sound (w := (351208926627 / 1351208926627)) (n := 12)
    (lo := (532049507 / 1000000000)) (hi := (133012377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851208926627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851208926627 / 500000000000) = 1/(500000000000 / 851208926627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (532049507 / 1000000000) (133012377 / 250000000) (Real.log (851208926627 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (851208926627 / 500000000000) = -Real.log (500000000000 / 851208926627) := by
    rw [show ((851208926627 / 500000000000) : ℝ) = ((500000000000 / 851208926627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94603477 / 250000000) ≤ -Real.log (500000000000 / 729983555119) ∧
    -Real.log (500000000000 / 729983555119) ≤ (378413909 / 1000000000) := by
  have h := checkLog_sound (w := (229983555119 / 1229983555119)) (n := 12)
    (lo := (94603477 / 250000000)) (hi := (378413909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729983555119 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729983555119 / 500000000000) = 1/(500000000000 / 729983555119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94603477 / 250000000) (378413909 / 1000000000) (Real.log (729983555119 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (729983555119 / 500000000000) = -Real.log (500000000000 / 729983555119) := by
    rw [show ((729983555119 / 500000000000) : ℝ) = ((500000000000 / 729983555119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (379070917 / 1000000000) ≤ -Real.log (500000000000 / 730463318659) ∧
    -Real.log (500000000000 / 730463318659) ≤ (189535459 / 500000000) := by
  have h := checkLog_sound (w := (230463318659 / 1230463318659)) (n := 12)
    (lo := (379070917 / 1000000000)) (hi := (189535459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730463318659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730463318659 / 500000000000) = 1/(500000000000 / 730463318659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (379070917 / 1000000000) (189535459 / 500000000) (Real.log (730463318659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (730463318659 / 500000000000) = -Real.log (500000000000 / 730463318659) := by
    rw [show ((730463318659 / 500000000000) : ℝ) = ((500000000000 / 730463318659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35710643 / 1000000000) ≤ -Real.log (241229864799 / 250000000000) ∧
    -Real.log (241229864799 / 250000000000) ≤ (8927661 / 250000000) := by
  have h := checkLog_sound (w := (8770135201 / 491229864799)) (n := 12)
    (lo := (35710643 / 1000000000)) (hi := (8927661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241229864799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241229864799) = 1/(241229864799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8927661 / 250000000) (-35710643 / 1000000000) (Real.log (241229864799 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3558769 / 100000000) ≤ -Real.log (965038105639 / 1000000000000) ∧
    -Real.log (965038105639 / 1000000000000) ≤ (35587691 / 1000000000) := by
  have h := checkLog_sound (w := (34961894361 / 1965038105639)) (n := 12)
    (lo := (3558769 / 100000000)) (hi := (35587691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965038105639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965038105639) = 1/(965038105639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35587691 / 1000000000) (-3558769 / 100000000) (Real.log (965038105639 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell196

end


