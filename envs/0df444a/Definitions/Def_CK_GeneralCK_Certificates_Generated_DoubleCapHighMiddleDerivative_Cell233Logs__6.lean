-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell233Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell233Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:47:04.730703+00:00
-- url     : https://prove2.me/theorems/883c8933-ca06-45db-9566-e67d84727733
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell233Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell234…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell233Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell234Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell235Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell236Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell237Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell238Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell233Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell234Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell235Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell236Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell237Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell238Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell233Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell234Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell235Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell236Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell237Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell238Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell233Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell234Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell235Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell236Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell237Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell238Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell233Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell233
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

theorem reflection_log_1_neg : (65444399 / 200000000) ≤ -Real.log (2560 / 3551) ∧
    -Real.log (2560 / 3551) ≤ (81805499 / 250000000) := by
  have h := checkLog_sound (w := (991 / 6111)) (n := 12)
    (lo := (65444399 / 200000000)) (hi := (81805499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3551 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3551 / 2560) = 1/(2560 / 3551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65444399 / 200000000) (81805499 / 250000000) (Real.log (3551 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3551 / 2560) = -Real.log (2560 / 3551) := by
    rw [show ((3551 / 2560) : ℝ) = ((2560 / 3551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30598049 / 62500000) ≤ -Real.log (1569 / 2560) ∧
    -Real.log (1569 / 2560) ≤ (97913757 / 200000000) := by
  have h := checkLog_sound (w := (991 / 4129)) (n := 12)
    (lo := (30598049 / 62500000)) (hi := (97913757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1569) = 1/(1569 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-97913757 / 200000000) (-30598049 / 62500000) (Real.log (1569 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32679949 / 100000000) ≤ -Real.log (5120 / 7099) ∧
    -Real.log (5120 / 7099) ≤ (326799491 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 12219)) (n := 12)
    (lo := (32679949 / 100000000)) (hi := (326799491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7099 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7099 / 5120) = 1/(5120 / 7099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32679949 / 100000000) (326799491 / 1000000000) (Real.log (7099 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7099 / 5120) = -Real.log (5120 / 7099) := by
    rw [show ((7099 / 5120) : ℝ) = ((5120 / 7099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244306609 / 500000000) ≤ -Real.log (3141 / 5120) ∧
    -Real.log (3141 / 5120) ≤ (488613219 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 8261)) (n := 12)
    (lo := (244306609 / 500000000)) (hi := (488613219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3141) = 1/(3141 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-488613219 / 1000000000) (-244306609 / 500000000) (Real.log (3141 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (243047349 / 1000000000) ≤ -Real.log (1000000 / 1275129) ∧
    -Real.log (1000000 / 1275129) ≤ (4860947 / 20000000) := by
  have h := checkLog_sound (w := (275129 / 2275129)) (n := 12)
    (lo := (243047349 / 1000000000)) (hi := (4860947 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275129 / 1000000) = 1/(1000000 / 1275129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (243047349 / 1000000000) (4860947 / 20000000) (Real.log (1275129 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1275129 / 1000000) = -Real.log (1000000 / 1275129) := by
    rw [show ((1275129 / 1000000) : ℝ) = ((1000000 / 1275129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (32176157 / 100000000) ≤ -Real.log (724871 / 1000000) ∧
    -Real.log (724871 / 1000000) ≤ (321761571 / 1000000000) := by
  have h := checkLog_sound (w := (275129 / 1724871)) (n := 12)
    (lo := (32176157 / 100000000)) (hi := (321761571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724871) = 1/(724871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-321761571 / 1000000000) (-32176157 / 100000000) (Real.log (724871 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24337981 / 100000000) ≤ -Real.log (1000000 / 1275553) ∧
    -Real.log (1000000 / 1275553) ≤ (243379811 / 1000000000) := by
  have h := checkLog_sound (w := (275553 / 2275553)) (n := 12)
    (lo := (24337981 / 100000000)) (hi := (243379811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275553 / 1000000) = 1/(1000000 / 1275553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24337981 / 100000000) (243379811 / 1000000000) (Real.log (1275553 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1275553 / 1000000) = -Real.log (1000000 / 1275553) := by
    rw [show ((1275553 / 1000000) : ℝ) = ((1000000 / 1275553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (322346673 / 1000000000) ≤ -Real.log (724447 / 1000000) ∧
    -Real.log (724447 / 1000000) ≤ (161173337 / 500000000) := by
  have h := checkLog_sound (w := (275553 / 1724447)) (n := 12)
    (lo := (322346673 / 1000000000)) (hi := (161173337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724447) = 1/(724447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-161173337 / 500000000) (-322346673 / 1000000000) (Real.log (724447 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45311703 / 250000000) ≤ -Real.log (1000000 / 1198711) ∧
    -Real.log (1000000 / 1198711) ≤ (181246813 / 1000000000) := by
  have h := checkLog_sound (w := (198711 / 2198711)) (n := 12)
    (lo := (45311703 / 250000000)) (hi := (181246813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198711 / 1000000) = 1/(1000000 / 1198711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45311703 / 250000000) (181246813 / 1000000000) (Real.log (1198711 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1198711 / 1000000) = -Real.log (1000000 / 1198711) := by
    rw [show ((1198711 / 1000000) : ℝ) = ((1000000 / 1198711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (221533597 / 1000000000) ≤ -Real.log (801289 / 1000000) ∧
    -Real.log (801289 / 1000000) ≤ (110766799 / 500000000) := by
  have h := checkLog_sound (w := (198711 / 1801289)) (n := 12)
    (lo := (221533597 / 1000000000)) (hi := (110766799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801289) = 1/(801289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110766799 / 500000000) (-221533597 / 1000000000) (Real.log (801289 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18151373 / 100000000) ≤ -Real.log (1000000 / 1199031) ∧
    -Real.log (1000000 / 1199031) ≤ (181513731 / 1000000000) := by
  have h := checkLog_sound (w := (199031 / 2199031)) (n := 12)
    (lo := (18151373 / 100000000)) (hi := (181513731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199031 / 1000000) = 1/(1000000 / 1199031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18151373 / 100000000) (181513731 / 1000000000) (Real.log (1199031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199031 / 1000000) = -Real.log (1000000 / 1199031) := by
    rw [show ((1199031 / 1000000) : ℝ) = ((1000000 / 1199031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (110966517 / 500000000) ≤ -Real.log (800969 / 1000000) ∧
    -Real.log (800969 / 1000000) ≤ (44386607 / 200000000) := by
  have h := checkLog_sound (w := (199031 / 1800969)) (n := 12)
    (lo := (110966517 / 500000000)) (hi := (44386607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800969) = 1/(800969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44386607 / 200000000) (-110966517 / 500000000) (Real.log (800969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (815412707 / 1000000000) ≤ -Real.log (50000000000 / 113005412289) ∧
    -Real.log (50000000000 / 113005412289) ≤ (815412709 / 1000000000) := by
  have h := checkLog_sound (w := (13005412289 / 213005412289)) (n := 12)
    (lo := (122265527 / 1000000000)) (hi := (15283191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113005412289 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113005412289 / 100000000000) = 1/(50000000000 / 113005412289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (815412707 / 1000000000) (815412709 / 1000000000) (Real.log (113005412289 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (113005412289 / 50000000000) = -Real.log (50000000000 / 113005412289) := by
    rw [show ((113005412289 / 50000000000) : ℝ) = ((50000000000 / 113005412289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (816790779 / 1000000000) ≤ -Real.log (250000000000 / 565806246017) ∧
    -Real.log (250000000000 / 565806246017) ≤ (816790781 / 1000000000) := by
  have h := checkLog_sound (w := (65806246017 / 1065806246017)) (n := 12)
    (lo := (123643599 / 1000000000)) (hi := (309109 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565806246017 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565806246017 / 500000000000) = 1/(250000000000 / 565806246017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (816790779 / 1000000000) (816790781 / 1000000000) (Real.log (565806246017 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (565806246017 / 250000000000) = -Real.log (250000000000 / 565806246017) := by
    rw [show ((565806246017 / 250000000000) : ℝ) = ((250000000000 / 565806246017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (14120223 / 25000000) ≤ -Real.log (25000000000 / 43977790531) ∧
    -Real.log (25000000000 / 43977790531) ≤ (564808921 / 1000000000) := by
  have h := checkLog_sound (w := (18977790531 / 68977790531)) (n := 12)
    (lo := (14120223 / 25000000)) (hi := (564808921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43977790531 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43977790531 / 25000000000) = 1/(25000000000 / 43977790531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14120223 / 25000000) (564808921 / 1000000000) (Real.log (43977790531 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (43977790531 / 25000000000) = -Real.log (25000000000 / 43977790531) := by
    rw [show ((43977790531 / 25000000000) : ℝ) = ((25000000000 / 43977790531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (565726483 / 1000000000) ≤ -Real.log (500000000000 / 880363228781) ∧
    -Real.log (500000000000 / 880363228781) ≤ (141431621 / 250000000) := by
  have h := checkLog_sound (w := (380363228781 / 1380363228781)) (n := 12)
    (lo := (565726483 / 1000000000)) (hi := (141431621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880363228781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880363228781 / 500000000000) = 1/(500000000000 / 880363228781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (565726483 / 1000000000) (141431621 / 250000000) (Real.log (880363228781 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (880363228781 / 500000000000) = -Real.log (500000000000 / 880363228781) := by
    rw [show ((880363228781 / 500000000000) : ℝ) = ((500000000000 / 880363228781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40278041 / 100000000) ≤ -Real.log (500000000000 / 747989177437) ∧
    -Real.log (500000000000 / 747989177437) ≤ (402780411 / 1000000000) := by
  have h := checkLog_sound (w := (247989177437 / 1247989177437)) (n := 12)
    (lo := (40278041 / 100000000)) (hi := (402780411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747989177437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747989177437 / 500000000000) = 1/(500000000000 / 747989177437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40278041 / 100000000) (402780411 / 1000000000) (Real.log (747989177437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (747989177437 / 500000000000) = -Real.log (500000000000 / 747989177437) := by
    rw [show ((747989177437 / 500000000000) : ℝ) = ((500000000000 / 747989177437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (100861691 / 250000000) ≤ -Real.log (50000000000 / 74848776919) ∧
    -Real.log (50000000000 / 74848776919) ≤ (80689353 / 200000000) := by
  have h := checkLog_sound (w := (24848776919 / 124848776919)) (n := 12)
    (lo := (100861691 / 250000000)) (hi := (80689353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74848776919 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74848776919 / 50000000000) = 1/(50000000000 / 74848776919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (100861691 / 250000000) (80689353 / 200000000) (Real.log (74848776919 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (74848776919 / 50000000000) = -Real.log (50000000000 / 74848776919) := by
    rw [show ((74848776919 / 50000000000) : ℝ) = ((50000000000 / 74848776919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40419303 / 1000000000) ≤ -Real.log (960386661039 / 1000000000000) ∧
    -Real.log (960386661039 / 1000000000000) ≤ (5052413 / 125000000) := by
  have h := checkLog_sound (w := (39613338961 / 1960386661039)) (n := 12)
    (lo := (40419303 / 1000000000)) (hi := (5052413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960386661039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960386661039) = 1/(960386661039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5052413 / 125000000) (-40419303 / 1000000000) (Real.log (960386661039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8057357 / 200000000) ≤ -Real.log (960513938479 / 1000000000000) ∧
    -Real.log (960513938479 / 1000000000000) ≤ (20143393 / 500000000) := by
  have h := checkLog_sound (w := (39486061521 / 1960513938479)) (n := 12)
    (lo := (8057357 / 200000000)) (hi := (20143393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960513938479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960513938479) = 1/(960513938479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20143393 / 500000000) (-8057357 / 200000000) (Real.log (960513938479 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell233

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell234Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell234
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

theorem reflection_log_1_neg : (163822161 / 500000000) ≤ -Real.log (1024 / 1421) ∧
    -Real.log (1024 / 1421) ≤ (327644323 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2445)) (n := 12)
    (lo := (163822161 / 500000000)) (hi := (327644323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1024) = 1/(1024 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (163822161 / 500000000) (327644323 / 1000000000) (Real.log (1421 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1421 / 1024) = -Real.log (1024 / 1421) := by
    rw [show ((1421 / 1024) : ℝ) = ((1024 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30657829 / 62500000) ≤ -Real.log (627 / 1024) ∧
    -Real.log (627 / 1024) ≤ (98105053 / 200000000) := by
  have h := checkLog_sound (w := (397 / 1651)) (n := 12)
    (lo := (30657829 / 62500000)) (hi := (98105053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 627) = 1/(627 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-98105053 / 200000000) (-30657829 / 62500000) (Real.log (627 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65444399 / 200000000) ≤ -Real.log (2560 / 3551) ∧
    -Real.log (2560 / 3551) ≤ (81805499 / 250000000) := by
  have h := checkLog_sound (w := (991 / 6111)) (n := 12)
    (lo := (65444399 / 200000000)) (hi := (81805499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3551 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3551 / 2560) = 1/(2560 / 3551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65444399 / 200000000) (81805499 / 250000000) (Real.log (3551 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3551 / 2560) = -Real.log (2560 / 3551) := by
    rw [show ((3551 / 2560) : ℝ) = ((2560 / 3551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30598049 / 62500000) ≤ -Real.log (1569 / 2560) ∧
    -Real.log (1569 / 2560) ≤ (97913757 / 200000000) := by
  have h := checkLog_sound (w := (991 / 4129)) (n := 12)
    (lo := (30598049 / 62500000)) (hi := (97913757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1569) = 1/(1569 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-97913757 / 200000000) (-30598049 / 62500000) (Real.log (1569 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121689513 / 500000000) ≤ -Real.log (31250 / 39861) ∧
    -Real.log (31250 / 39861) ≤ (243379027 / 1000000000) := by
  have h := checkLog_sound (w := (8611 / 71111)) (n := 12)
    (lo := (121689513 / 500000000)) (hi := (243379027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39861 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39861 / 31250) = 1/(31250 / 39861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121689513 / 500000000) (243379027 / 1000000000) (Real.log (39861 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (39861 / 31250) = -Real.log (31250 / 39861) := by
    rw [show ((39861 / 31250) : ℝ) = ((31250 / 39861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (322345293 / 1000000000) ≤ -Real.log (22639 / 31250) ∧
    -Real.log (22639 / 31250) ≤ (161172647 / 500000000) := by
  have h := checkLog_sound (w := (8611 / 53889)) (n := 12)
    (lo := (322345293 / 1000000000)) (hi := (161172647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22639) = 1/(22639 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-161172647 / 500000000) (-322345293 / 1000000000) (Real.log (22639 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1949691 / 8000000) ≤ -Real.log (125000 / 159497) ∧
    -Real.log (125000 / 159497) ≤ (15231961 / 62500000) := by
  have h := checkLog_sound (w := (34497 / 284497)) (n := 12)
    (lo := (1949691 / 8000000)) (hi := (15231961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159497 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159497 / 125000) = 1/(125000 / 159497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1949691 / 8000000) (15231961 / 62500000) (Real.log (159497 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (159497 / 125000) = -Real.log (125000 / 159497) := by
    rw [show ((159497 / 125000) : ℝ) = ((125000 / 159497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (322930737 / 1000000000) ≤ -Real.log (90503 / 125000) ∧
    -Real.log (90503 / 125000) ≤ (161465369 / 500000000) := by
  have h := checkLog_sound (w := (34497 / 215503)) (n := 12)
    (lo := (322930737 / 1000000000)) (hi := (161465369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90503) = 1/(90503 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-161465369 / 500000000) (-322930737 / 1000000000) (Real.log (90503 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2836139 / 15625000) ≤ -Real.log (100000 / 119903) ∧
    -Real.log (100000 / 119903) ≤ (181512897 / 1000000000) := by
  have h := checkLog_sound (w := (19903 / 219903)) (n := 12)
    (lo := (2836139 / 15625000)) (hi := (181512897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119903 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119903 / 100000) = 1/(100000 / 119903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2836139 / 15625000) (181512897 / 1000000000) (Real.log (119903 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119903 / 100000) = -Real.log (100000 / 119903) := by
    rw [show ((119903 / 100000) : ℝ) = ((100000 / 119903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44386357 / 200000000) ≤ -Real.log (80097 / 100000) ∧
    -Real.log (80097 / 100000) ≤ (110965893 / 500000000) := by
  have h := checkLog_sound (w := (19903 / 180097)) (n := 12)
    (lo := (44386357 / 200000000)) (hi := (110965893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80097) = 1/(80097 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110965893 / 500000000) (-44386357 / 200000000) (Real.log (80097 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (181778909 / 1000000000) ≤ -Real.log (1000000 / 1199349) ∧
    -Real.log (1000000 / 1199349) ≤ (18177891 / 100000000) := by
  have h := checkLog_sound (w := (199349 / 2199349)) (n := 12)
    (lo := (181778909 / 1000000000)) (hi := (18177891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199349 / 1000000) = 1/(1000000 / 1199349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (181778909 / 1000000000) (18177891 / 100000000) (Real.log (1199349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199349 / 1000000) = -Real.log (1000000 / 1199349) := by
    rw [show ((1199349 / 1000000) : ℝ) = ((1000000 / 1199349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55582533 / 250000000) ≤ -Real.log (800651 / 1000000) ∧
    -Real.log (800651 / 1000000) ≤ (222330133 / 1000000000) := by
  have h := checkLog_sound (w := (199349 / 1800651)) (n := 12)
    (lo := (55582533 / 250000000)) (hi := (222330133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800651) = 1/(800651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-222330133 / 1000000000) (-55582533 / 250000000) (Real.log (800651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (816790779 / 1000000000) ≤ -Real.log (500000000000 / 1131612492033) ∧
    -Real.log (500000000000 / 1131612492033) ≤ (816790781 / 1000000000) := by
  have h := checkLog_sound (w := (131612492033 / 2131612492033)) (n := 12)
    (lo := (123643599 / 1000000000)) (hi := (309109 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131612492033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131612492033 / 1000000000000) = 1/(500000000000 / 1131612492033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (816790779 / 1000000000) (816790781 / 1000000000) (Real.log (1131612492033 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1131612492033 / 500000000000) = -Real.log (500000000000 / 1131612492033) := by
    rw [show ((1131612492033 / 500000000000) : ℝ) = ((500000000000 / 1131612492033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (409084793 / 500000000) ≤ -Real.log (500000000000 / 1133173843701) ∧
    -Real.log (500000000000 / 1133173843701) ≤ (204542397 / 250000000) := by
  have h := checkLog_sound (w := (133173843701 / 2133173843701)) (n := 12)
    (lo := (62511203 / 500000000)) (hi := (125022407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133173843701 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1133173843701 / 1000000000000) = 1/(500000000000 / 1133173843701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (409084793 / 500000000) (204542397 / 250000000) (Real.log (1133173843701 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1133173843701 / 500000000000) = -Real.log (500000000000 / 1133173843701) := by
    rw [show ((1133173843701 / 500000000000) : ℝ) = ((500000000000 / 1133173843701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (565724319 / 1000000000) ≤ -Real.log (25000000000 / 44018066169) ∧
    -Real.log (25000000000 / 44018066169) ≤ (3535777 / 6250000) := by
  have h := checkLog_sound (w := (19018066169 / 69018066169)) (n := 12)
    (lo := (565724319 / 1000000000)) (hi := (3535777 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44018066169 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44018066169 / 25000000000) = 1/(25000000000 / 44018066169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (565724319 / 1000000000) (3535777 / 6250000) (Real.log (44018066169 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (44018066169 / 25000000000) = -Real.log (25000000000 / 44018066169) := by
    rw [show ((44018066169 / 25000000000) : ℝ) = ((25000000000 / 44018066169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (566642113 / 1000000000) ≤ -Real.log (500000000000 / 881169684983) ∧
    -Real.log (500000000000 / 881169684983) ≤ (283321057 / 500000000) := by
  have h := checkLog_sound (w := (381169684983 / 1381169684983)) (n := 12)
    (lo := (566642113 / 1000000000)) (hi := (283321057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881169684983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881169684983 / 500000000000) = 1/(500000000000 / 881169684983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (566642113 / 1000000000) (283321057 / 500000000) (Real.log (881169684983 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (881169684983 / 500000000000) = -Real.log (500000000000 / 881169684983) := by
    rw [show ((881169684983 / 500000000000) : ℝ) = ((500000000000 / 881169684983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (201722341 / 500000000) ≤ -Real.log (500000000000 / 748486210469) ∧
    -Real.log (500000000000 / 748486210469) ≤ (403444683 / 1000000000) := by
  have h := checkLog_sound (w := (248486210469 / 1248486210469)) (n := 12)
    (lo := (201722341 / 500000000)) (hi := (403444683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748486210469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748486210469 / 500000000000) = 1/(500000000000 / 748486210469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (201722341 / 500000000) (403444683 / 1000000000) (Real.log (748486210469 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (748486210469 / 500000000000) = -Real.log (500000000000 / 748486210469) := by
    rw [show ((748486210469 / 500000000000) : ℝ) = ((500000000000 / 748486210469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404109041 / 1000000000) ≤ -Real.log (125000000000 / 187245909891) ∧
    -Real.log (125000000000 / 187245909891) ≤ (202054521 / 500000000) := by
  have h := checkLog_sound (w := (62245909891 / 312245909891)) (n := 12)
    (lo := (404109041 / 1000000000)) (hi := (202054521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187245909891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187245909891 / 125000000000) = 1/(125000000000 / 187245909891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404109041 / 1000000000) (202054521 / 500000000) (Real.log (187245909891 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (187245909891 / 125000000000) = -Real.log (125000000000 / 187245909891) := by
    rw [show ((187245909891 / 125000000000) : ℝ) = ((125000000000 / 187245909891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20275611 / 500000000) ≤ -Real.log (960259976199 / 1000000000000) ∧
    -Real.log (960259976199 / 1000000000000) ≤ (40551223 / 1000000000) := by
  have h := checkLog_sound (w := (39740023801 / 1960259976199)) (n := 12)
    (lo := (20275611 / 500000000)) (hi := (40551223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960259976199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960259976199) = 1/(960259976199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40551223 / 1000000000) (-20275611 / 500000000) (Real.log (960259976199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40418889 / 1000000000) ≤ -Real.log (9603870591 / 10000000000) ∧
    -Real.log (9603870591 / 10000000000) ≤ (4041889 / 100000000) := by
  have h := checkLog_sound (w := (396129409 / 19603870591)) (n := 12)
    (lo := (40418889 / 1000000000)) (hi := (4041889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9603870591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9603870591) = 1/(9603870591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4041889 / 100000000) (-40418889 / 1000000000) (Real.log (9603870591 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell234

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell235Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell235
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

theorem reflection_log_1_neg : (328066471 / 1000000000) ≤ -Real.log (1280 / 1777) ∧
    -Real.log (1280 / 1777) ≤ (41008309 / 125000000) := by
  have h := checkLog_sound (w := (497 / 3057)) (n := 12)
    (lo := (328066471 / 1000000000)) (hi := (41008309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777 / 1280) = 1/(1280 / 1777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (328066471 / 1000000000) (41008309 / 125000000) (Real.log (1777 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1777 / 1280) = -Real.log (1280 / 1777) := by
    rw [show ((1777 / 1280) : ℝ) = ((1280 / 1777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24574133 / 50000000) ≤ -Real.log (783 / 1280) ∧
    -Real.log (783 / 1280) ≤ (491482661 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2063)) (n := 12)
    (lo := (24574133 / 50000000)) (hi := (491482661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 783) = 1/(783 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-491482661 / 1000000000) (-24574133 / 50000000) (Real.log (783 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (163822161 / 500000000) ≤ -Real.log (1024 / 1421) ∧
    -Real.log (1024 / 1421) ≤ (327644323 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2445)) (n := 12)
    (lo := (163822161 / 500000000)) (hi := (327644323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1024) = 1/(1024 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (163822161 / 500000000) (327644323 / 1000000000) (Real.log (1421 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1421 / 1024) = -Real.log (1024 / 1421) := by
    rw [show ((1421 / 1024) : ℝ) = ((1024 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30657829 / 62500000) ≤ -Real.log (627 / 1024) ∧
    -Real.log (627 / 1024) ≤ (98105053 / 200000000) := by
  have h := checkLog_sound (w := (397 / 1651)) (n := 12)
    (lo := (30657829 / 62500000)) (hi := (98105053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 627) = 1/(627 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-98105053 / 200000000) (-30657829 / 62500000) (Real.log (627 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1903989 / 7812500) ≤ -Real.log (40000 / 51039) ∧
    -Real.log (40000 / 51039) ≤ (243710593 / 1000000000) := by
  have h := checkLog_sound (w := (11039 / 91039)) (n := 12)
    (lo := (1903989 / 7812500)) (hi := (243710593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51039 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51039 / 40000) = 1/(40000 / 51039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1903989 / 7812500) (243710593 / 1000000000) (Real.log (51039 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (51039 / 40000) = -Real.log (40000 / 51039) := by
    rw [show ((51039 / 40000) : ℝ) = ((40000 / 51039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (80732339 / 250000000) ≤ -Real.log (28961 / 40000) ∧
    -Real.log (28961 / 40000) ≤ (322929357 / 1000000000) := by
  have h := checkLog_sound (w := (11039 / 68961)) (n := 12)
    (lo := (80732339 / 250000000)) (hi := (322929357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28961) = 1/(28961 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-322929357 / 1000000000) (-80732339 / 250000000) (Real.log (28961 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (244042831 / 1000000000) ≤ -Real.log (1000000 / 1276399) ∧
    -Real.log (1000000 / 1276399) ≤ (15252677 / 62500000) := by
  have h := checkLog_sound (w := (276399 / 2276399)) (n := 12)
    (lo := (244042831 / 1000000000)) (hi := (15252677 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276399 / 1000000) = 1/(1000000 / 1276399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (244042831 / 1000000000) (15252677 / 62500000) (Real.log (1276399 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1276399 / 1000000) = -Real.log (1000000 / 1276399) := by
    rw [show ((1276399 / 1000000) : ℝ) = ((1000000 / 1276399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323515143 / 1000000000) ≤ -Real.log (723601 / 1000000) ∧
    -Real.log (723601 / 1000000) ≤ (40439393 / 125000000) := by
  have h := checkLog_sound (w := (276399 / 1723601)) (n := 12)
    (lo := (323515143 / 1000000000)) (hi := (40439393 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723601) = 1/(723601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40439393 / 125000000) (-323515143 / 1000000000) (Real.log (723601 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7271123 / 40000000) ≤ -Real.log (250000 / 299837) ∧
    -Real.log (250000 / 299837) ≤ (45444519 / 250000000) := by
  have h := checkLog_sound (w := (49837 / 549837)) (n := 12)
    (lo := (7271123 / 40000000)) (hi := (45444519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299837 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299837 / 250000) = 1/(250000 / 299837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7271123 / 40000000) (45444519 / 250000000) (Real.log (299837 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299837 / 250000) = -Real.log (250000 / 299837) := by
    rw [show ((299837 / 250000) : ℝ) = ((250000 / 299837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (222328883 / 1000000000) ≤ -Real.log (200163 / 250000) ∧
    -Real.log (200163 / 250000) ≤ (55582221 / 250000000) := by
  have h := checkLog_sound (w := (49837 / 450163)) (n := 12)
    (lo := (222328883 / 1000000000)) (hi := (55582221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200163) = 1/(200163 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55582221 / 250000000) (-222328883 / 1000000000) (Real.log (200163 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182044851 / 1000000000) ≤ -Real.log (250000 / 299917) ∧
    -Real.log (250000 / 299917) ≤ (45511213 / 250000000) := by
  have h := checkLog_sound (w := (49917 / 549917)) (n := 12)
    (lo := (182044851 / 1000000000)) (hi := (45511213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299917 / 250000) = 1/(250000 / 299917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182044851 / 1000000000) (45511213 / 250000000) (Real.log (299917 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (299917 / 250000) = -Real.log (250000 / 299917) := by
    rw [show ((299917 / 250000) : ℝ) = ((250000 / 299917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (222728637 / 1000000000) ≤ -Real.log (200083 / 250000) ∧
    -Real.log (200083 / 250000) ≤ (111364319 / 500000000) := by
  have h := checkLog_sound (w := (49917 / 450083)) (n := 12)
    (lo := (222728637 / 1000000000)) (hi := (111364319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200083) = 1/(200083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111364319 / 500000000) (-222728637 / 1000000000) (Real.log (200083 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (409084793 / 500000000) ≤ -Real.log (5000000000 / 11331738437) ∧
    -Real.log (5000000000 / 11331738437) ≤ (204542397 / 250000000) := by
  have h := checkLog_sound (w := (1331738437 / 21331738437)) (n := 12)
    (lo := (62511203 / 500000000)) (hi := (125022407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11331738437 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11331738437 / 10000000000) = 1/(5000000000 / 11331738437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (409084793 / 500000000) (204542397 / 250000000) (Real.log (11331738437 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (11331738437 / 5000000000) = -Real.log (5000000000 / 11331738437) := by
    rw [show ((11331738437 / 5000000000) : ℝ) = ((5000000000 / 11331738437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (819549131 / 1000000000) ≤ -Real.log (500000000000 / 1134738186463) ∧
    -Real.log (500000000000 / 1134738186463) ≤ (819549133 / 1000000000) := by
  have h := checkLog_sound (w := (134738186463 / 2134738186463)) (n := 12)
    (lo := (126401951 / 1000000000)) (hi := (3950061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134738186463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1134738186463 / 1000000000000) = 1/(500000000000 / 1134738186463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (819549131 / 1000000000) (819549133 / 1000000000) (Real.log (1134738186463 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1134738186463 / 500000000000) = -Real.log (500000000000 / 1134738186463) := by
    rw [show ((1134738186463 / 500000000000) : ℝ) = ((500000000000 / 1134738186463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (566639949 / 1000000000) ≤ -Real.log (100000000000 / 176233555471) ∧
    -Real.log (100000000000 / 176233555471) ≤ (11332799 / 20000000) := by
  have h := checkLog_sound (w := (76233555471 / 276233555471)) (n := 12)
    (lo := (566639949 / 1000000000)) (hi := (11332799 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176233555471 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176233555471 / 100000000000) = 1/(100000000000 / 176233555471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (566639949 / 1000000000) (11332799 / 20000000) (Real.log (176233555471 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (176233555471 / 100000000000) = -Real.log (100000000000 / 176233555471) := by
    rw [show ((176233555471 / 100000000000) : ℝ) = ((100000000000 / 176233555471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22702319 / 40000000) ≤ -Real.log (62500000000 / 110247135507) ∧
    -Real.log (62500000000 / 110247135507) ≤ (70944747 / 125000000) := by
  have h := checkLog_sound (w := (47747135507 / 172747135507)) (n := 12)
    (lo := (22702319 / 40000000)) (hi := (70944747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110247135507 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110247135507 / 62500000000) = 1/(62500000000 / 110247135507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (22702319 / 40000000) (70944747 / 125000000) (Real.log (110247135507 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (110247135507 / 62500000000) = -Real.log (62500000000 / 110247135507) := by
    rw [show ((110247135507 / 62500000000) : ℝ) = ((62500000000 / 110247135507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (404106959 / 1000000000) ≤ -Real.log (100000000000 / 149796415921) ∧
    -Real.log (100000000000 / 149796415921) ≤ (5051337 / 12500000) := by
  have h := checkLog_sound (w := (49796415921 / 249796415921)) (n := 12)
    (lo := (404106959 / 1000000000)) (hi := (5051337 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149796415921 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149796415921 / 100000000000) = 1/(100000000000 / 149796415921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (404106959 / 1000000000) (5051337 / 12500000) (Real.log (149796415921 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (149796415921 / 100000000000) = -Real.log (100000000000 / 149796415921) := by
    rw [show ((149796415921 / 100000000000) : ℝ) = ((100000000000 / 149796415921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404773489 / 1000000000) ≤ -Real.log (62500000000 / 93685183149) ∧
    -Real.log (62500000000 / 93685183149) ≤ (40477349 / 100000000) := by
  have h := checkLog_sound (w := (31185183149 / 156185183149)) (n := 12)
    (lo := (404773489 / 1000000000)) (hi := (40477349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93685183149 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93685183149 / 62500000000) = 1/(62500000000 / 93685183149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404773489 / 1000000000) (40477349 / 100000000) (Real.log (93685183149 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (93685183149 / 62500000000) = -Real.log (62500000000 / 93685183149) := by
    rw [show ((93685183149 / 62500000000) : ℝ) = ((62500000000 / 93685183149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8136757 / 200000000) ≤ -Real.log (60008293111 / 62500000000) ∧
    -Real.log (60008293111 / 62500000000) ≤ (20341893 / 500000000) := by
  have h := checkLog_sound (w := (2491706889 / 122508293111)) (n := 12)
    (lo := (8136757 / 200000000)) (hi := (20341893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60008293111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60008293111) = 1/(60008293111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20341893 / 500000000) (-8136757 / 200000000) (Real.log (60008293111 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40550807 / 1000000000) ≤ -Real.log (60016273431 / 62500000000) ∧
    -Real.log (60016273431 / 62500000000) ≤ (5068851 / 125000000) := by
  have h := checkLog_sound (w := (2483726569 / 122516273431)) (n := 12)
    (lo := (40550807 / 1000000000)) (hi := (5068851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60016273431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60016273431) = 1/(60016273431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5068851 / 125000000) (-40550807 / 1000000000) (Real.log (60016273431 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell235

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell236Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell236
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

theorem reflection_log_1_neg : (328488441 / 1000000000) ≤ -Real.log (5120 / 7111) ∧
    -Real.log (5120 / 7111) ≤ (164244221 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 12231)) (n := 12)
    (lo := (328488441 / 1000000000)) (hi := (164244221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7111 / 5120) = 1/(5120 / 7111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (328488441 / 1000000000) (164244221 / 500000000) (Real.log (7111 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7111 / 5120) = -Real.log (5120 / 7111) := by
    rw [show ((7111 / 5120) : ℝ) = ((5120 / 7111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246220487 / 500000000) ≤ -Real.log (3129 / 5120) ∧
    -Real.log (3129 / 5120) ≤ (19697639 / 40000000) := by
  have h := checkLog_sound (w := (1991 / 8249)) (n := 12)
    (lo := (246220487 / 500000000)) (hi := (19697639 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3129) = 1/(3129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-19697639 / 40000000) (-246220487 / 500000000) (Real.log (3129 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (328066471 / 1000000000) ≤ -Real.log (1280 / 1777) ∧
    -Real.log (1280 / 1777) ≤ (41008309 / 125000000) := by
  have h := checkLog_sound (w := (497 / 3057)) (n := 12)
    (lo := (328066471 / 1000000000)) (hi := (41008309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777 / 1280) = 1/(1280 / 1777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (328066471 / 1000000000) (41008309 / 125000000) (Real.log (1777 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1777 / 1280) = -Real.log (1280 / 1777) := by
    rw [show ((1777 / 1280) : ℝ) = ((1280 / 1777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24574133 / 50000000) ≤ -Real.log (783 / 1280) ∧
    -Real.log (783 / 1280) ≤ (491482661 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2063)) (n := 12)
    (lo := (24574133 / 50000000)) (hi := (491482661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 783) = 1/(783 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-491482661 / 1000000000) (-24574133 / 50000000) (Real.log (783 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3813157 / 15625000) ≤ -Real.log (500000 / 638199) ∧
    -Real.log (500000 / 638199) ≤ (244042049 / 1000000000) := by
  have h := checkLog_sound (w := (138199 / 1138199)) (n := 12)
    (lo := (3813157 / 15625000)) (hi := (244042049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638199 / 500000) = 1/(500000 / 638199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3813157 / 15625000) (244042049 / 1000000000) (Real.log (638199 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (638199 / 500000) = -Real.log (500000 / 638199) := by
    rw [show ((638199 / 500000) : ℝ) = ((500000 / 638199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323513761 / 1000000000) ≤ -Real.log (361801 / 500000) ∧
    -Real.log (361801 / 500000) ≤ (161756881 / 500000000) := by
  have h := checkLog_sound (w := (138199 / 861801)) (n := 12)
    (lo := (323513761 / 1000000000)) (hi := (161756881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 361801) = 1/(361801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-161756881 / 500000000) (-323513761 / 1000000000) (Real.log (361801 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122187089 / 500000000) ≤ -Real.log (500000 / 638411) ∧
    -Real.log (500000 / 638411) ≤ (244374179 / 1000000000) := by
  have h := checkLog_sound (w := (138411 / 1138411)) (n := 12)
    (lo := (122187089 / 500000000)) (hi := (244374179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638411 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638411 / 500000) = 1/(500000 / 638411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122187089 / 500000000) (244374179 / 1000000000) (Real.log (638411 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (638411 / 500000) = -Real.log (500000 / 638411) := by
    rw [show ((638411 / 500000) : ℝ) = ((500000 / 638411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (32409989 / 100000000) ≤ -Real.log (361589 / 500000) ∧
    -Real.log (361589 / 500000) ≤ (324099891 / 1000000000) := by
  have h := checkLog_sound (w := (138411 / 861589)) (n := 12)
    (lo := (32409989 / 100000000)) (hi := (324099891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 361589) = 1/(361589 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324099891 / 1000000000) (-32409989 / 100000000) (Real.log (361589 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91022009 / 500000000) ≤ -Real.log (1000000 / 1199667) ∧
    -Real.log (1000000 / 1199667) ≤ (182044019 / 1000000000) := by
  have h := checkLog_sound (w := (199667 / 2199667)) (n := 12)
    (lo := (91022009 / 500000000)) (hi := (182044019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199667 / 1000000) = 1/(1000000 / 1199667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91022009 / 500000000) (182044019 / 1000000000) (Real.log (1199667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1199667 / 1000000) = -Real.log (1000000 / 1199667) := by
    rw [show ((1199667 / 1000000) : ℝ) = ((1000000 / 1199667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (222727387 / 1000000000) ≤ -Real.log (800333 / 1000000) ∧
    -Real.log (800333 / 1000000) ≤ (55681847 / 250000000) := by
  have h := checkLog_sound (w := (199667 / 1800333)) (n := 12)
    (lo := (222727387 / 1000000000)) (hi := (55681847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800333) = 1/(800333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55681847 / 250000000) (-222727387 / 1000000000) (Real.log (800333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182310723 / 1000000000) ≤ -Real.log (1000000 / 1199987) ∧
    -Real.log (1000000 / 1199987) ≤ (45577681 / 250000000) := by
  have h := checkLog_sound (w := (199987 / 2199987)) (n := 12)
    (lo := (182310723 / 1000000000)) (hi := (45577681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199987 / 1000000) = 1/(1000000 / 1199987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182310723 / 1000000000) (45577681 / 250000000) (Real.log (1199987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199987 / 1000000) = -Real.log (1000000 / 1199987) := by
    rw [show ((1199987 / 1000000) : ℝ) = ((1000000 / 1199987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (223127301 / 1000000000) ≤ -Real.log (800013 / 1000000) ∧
    -Real.log (800013 / 1000000) ≤ (111563651 / 500000000) := by
  have h := checkLog_sound (w := (199987 / 1800013)) (n := 12)
    (lo := (223127301 / 1000000000)) (hi := (111563651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800013) = 1/(800013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111563651 / 500000000) (-223127301 / 1000000000) (Real.log (800013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (819549131 / 1000000000) ≤ -Real.log (250000000000 / 567369093231) ∧
    -Real.log (250000000000 / 567369093231) ≤ (819549133 / 1000000000) := by
  have h := checkLog_sound (w := (67369093231 / 1067369093231)) (n := 12)
    (lo := (126401951 / 1000000000)) (hi := (3950061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567369093231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567369093231 / 500000000000) = 1/(250000000000 / 567369093231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (819549131 / 1000000000) (819549133 / 1000000000) (Real.log (567369093231 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (567369093231 / 250000000000) = -Real.log (250000000000 / 567369093231) := by
    rw [show ((567369093231 / 250000000000) : ℝ) = ((250000000000 / 567369093231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (164185883 / 200000000) ≤ -Real.log (500000000000 / 1136305528923) ∧
    -Real.log (500000000000 / 1136305528923) ≤ (820929417 / 1000000000) := by
  have h := checkLog_sound (w := (136305528923 / 2136305528923)) (n := 12)
    (lo := (25556447 / 200000000)) (hi := (31945559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136305528923 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1136305528923 / 1000000000000) = 1/(500000000000 / 1136305528923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (164185883 / 200000000) (820929417 / 1000000000) (Real.log (1136305528923 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1136305528923 / 500000000000) = -Real.log (500000000000 / 1136305528923) := by
    rw [show ((1136305528923 / 500000000000) : ℝ) = ((500000000000 / 1136305528923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (56755581 / 100000000) ≤ -Real.log (500000000000 / 881975174197) ∧
    -Real.log (500000000000 / 881975174197) ≤ (567555811 / 1000000000) := by
  have h := checkLog_sound (w := (381975174197 / 1381975174197)) (n := 12)
    (lo := (56755581 / 100000000)) (hi := (567555811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881975174197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881975174197 / 500000000000) = 1/(500000000000 / 881975174197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56755581 / 100000000) (567555811 / 1000000000) (Real.log (881975174197 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (881975174197 / 500000000000) = -Real.log (500000000000 / 881975174197) := by
    rw [show ((881975174197 / 500000000000) : ℝ) = ((500000000000 / 881975174197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (142118517 / 250000000) ≤ -Real.log (100000000000 / 176557085531) ∧
    -Real.log (100000000000 / 176557085531) ≤ (568474069 / 1000000000) := by
  have h := checkLog_sound (w := (76557085531 / 276557085531)) (n := 12)
    (lo := (142118517 / 250000000)) (hi := (568474069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176557085531 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176557085531 / 100000000000) = 1/(100000000000 / 176557085531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (142118517 / 250000000) (568474069 / 1000000000) (Real.log (176557085531 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (176557085531 / 100000000000) = -Real.log (100000000000 / 176557085531) := by
    rw [show ((176557085531 / 100000000000) : ℝ) = ((100000000000 / 176557085531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (202385703 / 500000000) ≤ -Real.log (500000000000 / 749479903989) ∧
    -Real.log (500000000000 / 749479903989) ≤ (404771407 / 1000000000) := by
  have h := checkLog_sound (w := (249479903989 / 1249479903989)) (n := 12)
    (lo := (202385703 / 500000000)) (hi := (404771407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749479903989 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749479903989 / 500000000000) = 1/(500000000000 / 749479903989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (202385703 / 500000000) (404771407 / 1000000000) (Real.log (749479903989 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (749479903989 / 500000000000) = -Real.log (500000000000 / 749479903989) := by
    rw [show ((749479903989 / 500000000000) : ℝ) = ((500000000000 / 749479903989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (50679753 / 125000000) ≤ -Real.log (500000000000 / 749979687831) ∧
    -Real.log (500000000000 / 749979687831) ≤ (16217521 / 40000000) := by
  have h := checkLog_sound (w := (249979687831 / 1249979687831)) (n := 12)
    (lo := (50679753 / 125000000)) (hi := (16217521 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749979687831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749979687831 / 500000000000) = 1/(500000000000 / 749979687831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (50679753 / 125000000) (16217521 / 40000000) (Real.log (749979687831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (749979687831 / 500000000000) = -Real.log (500000000000 / 749979687831) := by
    rw [show ((749979687831 / 500000000000) : ℝ) = ((500000000000 / 749979687831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20408289 / 500000000) ≤ -Real.log (960005199831 / 1000000000000) ∧
    -Real.log (960005199831 / 1000000000000) ≤ (40816579 / 1000000000) := by
  have h := checkLog_sound (w := (39994800169 / 1960005199831)) (n := 12)
    (lo := (20408289 / 500000000)) (hi := (40816579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960005199831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960005199831) = 1/(960005199831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40816579 / 1000000000) (-20408289 / 500000000) (Real.log (960005199831 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40683369 / 1000000000) ≤ -Real.log (960133089111 / 1000000000000) ∧
    -Real.log (960133089111 / 1000000000000) ≤ (4068337 / 100000000) := by
  have h := checkLog_sound (w := (39866910889 / 1960133089111)) (n := 12)
    (lo := (40683369 / 1000000000)) (hi := (4068337 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960133089111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960133089111) = 1/(960133089111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4068337 / 100000000) (-40683369 / 1000000000) (Real.log (960133089111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell236

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell237Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell237
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

theorem reflection_log_1_neg : (164455117 / 500000000) ≤ -Real.log (2560 / 3557) ∧
    -Real.log (2560 / 3557) ≤ (65782047 / 200000000) := by
  have h := checkLog_sound (w := (997 / 6117)) (n := 12)
    (lo := (164455117 / 500000000)) (hi := (65782047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3557 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3557 / 2560) = 1/(2560 / 3557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164455117 / 500000000) (65782047 / 200000000) (Real.log (3557 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3557 / 2560) = -Real.log (2560 / 3557) := by
    rw [show ((3557 / 2560) : ℝ) = ((2560 / 3557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (493400207 / 1000000000) ≤ -Real.log (1563 / 2560) ∧
    -Real.log (1563 / 2560) ≤ (30837513 / 62500000) := by
  have h := checkLog_sound (w := (997 / 4123)) (n := 12)
    (lo := (493400207 / 1000000000)) (hi := (30837513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1563) = 1/(1563 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30837513 / 62500000) (-493400207 / 1000000000) (Real.log (1563 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (328488441 / 1000000000) ≤ -Real.log (5120 / 7111) ∧
    -Real.log (5120 / 7111) ≤ (164244221 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 12231)) (n := 12)
    (lo := (328488441 / 1000000000)) (hi := (164244221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7111 / 5120) = 1/(5120 / 7111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (328488441 / 1000000000) (164244221 / 500000000) (Real.log (7111 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7111 / 5120) = -Real.log (5120 / 7111) := by
    rw [show ((7111 / 5120) : ℝ) = ((5120 / 7111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246220487 / 500000000) ≤ -Real.log (3129 / 5120) ∧
    -Real.log (3129 / 5120) ≤ (19697639 / 40000000) := by
  have h := checkLog_sound (w := (1991 / 8249)) (n := 12)
    (lo := (246220487 / 500000000)) (hi := (19697639 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3129) = 1/(3129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-19697639 / 40000000) (-246220487 / 500000000) (Real.log (3129 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122186697 / 500000000) ≤ -Real.log (1000000 / 1276821) ∧
    -Real.log (1000000 / 1276821) ≤ (48874679 / 200000000) := by
  have h := checkLog_sound (w := (276821 / 2276821)) (n := 12)
    (lo := (122186697 / 500000000)) (hi := (48874679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276821 / 1000000) = 1/(1000000 / 1276821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122186697 / 500000000) (48874679 / 200000000) (Real.log (1276821 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1276821 / 1000000) = -Real.log (1000000 / 1276821) := by
    rw [show ((1276821 / 1000000) : ℝ) = ((1000000 / 1276821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (324098507 / 1000000000) ≤ -Real.log (723179 / 1000000) ∧
    -Real.log (723179 / 1000000) ≤ (81024627 / 250000000) := by
  have h := checkLog_sound (w := (276821 / 1723179)) (n := 12)
    (lo := (324098507 / 1000000000)) (hi := (81024627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723179) = 1/(723179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-81024627 / 250000000) (-324098507 / 1000000000) (Real.log (723179 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122352707 / 500000000) ≤ -Real.log (200000 / 255449) ∧
    -Real.log (200000 / 255449) ≤ (48941083 / 200000000) := by
  have h := checkLog_sound (w := (55449 / 455449)) (n := 12)
    (lo := (122352707 / 500000000)) (hi := (48941083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255449 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(255449 / 200000) = 1/(200000 / 255449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122352707 / 500000000) (48941083 / 200000000) (Real.log (255449 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (255449 / 200000) = -Real.log (200000 / 255449) := by
    rw [show ((255449 / 200000) : ℝ) = ((200000 / 255449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16234249 / 50000000) ≤ -Real.log (144551 / 200000) ∧
    -Real.log (144551 / 200000) ≤ (324684981 / 1000000000) := by
  have h := checkLog_sound (w := (55449 / 344551)) (n := 12)
    (lo := (16234249 / 50000000)) (hi := (324684981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 144551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 144551) = 1/(144551 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324684981 / 1000000000) (-16234249 / 50000000) (Real.log (144551 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18230989 / 100000000) ≤ -Real.log (500000 / 599993) ∧
    -Real.log (500000 / 599993) ≤ (182309891 / 1000000000) := by
  have h := checkLog_sound (w := (99993 / 1099993)) (n := 12)
    (lo := (18230989 / 100000000)) (hi := (182309891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599993 / 500000) = 1/(500000 / 599993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18230989 / 100000000) (182309891 / 1000000000) (Real.log (599993 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (599993 / 500000) = -Real.log (500000 / 599993) := by
    rw [show ((599993 / 500000) : ℝ) = ((500000 / 599993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (223126051 / 1000000000) ≤ -Real.log (400007 / 500000) ∧
    -Real.log (400007 / 500000) ≤ (55781513 / 250000000) := by
  have h := checkLog_sound (w := (99993 / 900007)) (n := 12)
    (lo := (223126051 / 1000000000)) (hi := (55781513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400007) = 1/(400007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55781513 / 250000000) (-223126051 / 1000000000) (Real.log (400007 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45644131 / 250000000) ≤ -Real.log (500000 / 600153) ∧
    -Real.log (500000 / 600153) ≤ (7303061 / 40000000) := by
  have h := checkLog_sound (w := (100153 / 1100153)) (n := 12)
    (lo := (45644131 / 250000000)) (hi := (7303061 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600153 / 500000) = 1/(500000 / 600153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45644131 / 250000000) (7303061 / 40000000) (Real.log (600153 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600153 / 500000) = -Real.log (500000 / 600153) := by
    rw [show ((600153 / 500000) : ℝ) = ((500000 / 600153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55881531 / 250000000) ≤ -Real.log (399847 / 500000) ∧
    -Real.log (399847 / 500000) ≤ (1788209 / 8000000) := by
  have h := checkLog_sound (w := (100153 / 899847)) (n := 12)
    (lo := (55881531 / 250000000)) (hi := (1788209 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399847) = 1/(399847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1788209 / 8000000) (-55881531 / 250000000) (Real.log (399847 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (164185883 / 200000000) ≤ -Real.log (250000000000 / 568152764461) ∧
    -Real.log (250000000000 / 568152764461) ≤ (820929417 / 1000000000) := by
  have h := checkLog_sound (w := (68152764461 / 1068152764461)) (n := 12)
    (lo := (25556447 / 200000000)) (hi := (31945559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568152764461 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568152764461 / 500000000000) = 1/(250000000000 / 568152764461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (164185883 / 200000000) (820929417 / 1000000000) (Real.log (568152764461 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (568152764461 / 250000000000) = -Real.log (250000000000 / 568152764461) := by
    rw [show ((568152764461 / 250000000000) : ℝ) = ((250000000000 / 568152764461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20557761 / 25000000) ≤ -Real.log (500000000000 / 1137875879719) ∧
    -Real.log (500000000000 / 1137875879719) ≤ (411155221 / 500000000) := by
  have h := checkLog_sound (w := (137875879719 / 2137875879719)) (n := 12)
    (lo := (6458163 / 50000000)) (hi := (129163261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137875879719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1137875879719 / 1000000000000) = 1/(500000000000 / 1137875879719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (20557761 / 25000000) (411155221 / 500000000) (Real.log (1137875879719 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1137875879719 / 500000000000) = -Real.log (500000000000 / 1137875879719) := by
    rw [show ((1137875879719 / 500000000000) : ℝ) = ((500000000000 / 1137875879719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (284235951 / 500000000) ≤ -Real.log (500000000000 / 882783515561) ∧
    -Real.log (500000000000 / 882783515561) ≤ (568471903 / 1000000000) := by
  have h := checkLog_sound (w := (382783515561 / 1382783515561)) (n := 12)
    (lo := (284235951 / 500000000)) (hi := (568471903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((882783515561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(882783515561 / 500000000000) = 1/(500000000000 / 882783515561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (284235951 / 500000000) (568471903 / 1000000000) (Real.log (882783515561 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (882783515561 / 500000000000) = -Real.log (500000000000 / 882783515561) := by
    rw [show ((882783515561 / 500000000000) : ℝ) = ((500000000000 / 882783515561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (284695197 / 500000000) ≤ -Real.log (125000000000 / 220898679359) ∧
    -Real.log (125000000000 / 220898679359) ≤ (113878079 / 200000000) := by
  have h := checkLog_sound (w := (95898679359 / 345898679359)) (n := 12)
    (lo := (284695197 / 500000000)) (hi := (113878079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220898679359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220898679359 / 125000000000) = 1/(125000000000 / 220898679359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (284695197 / 500000000) (113878079 / 200000000) (Real.log (220898679359 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (220898679359 / 125000000000) = -Real.log (125000000000 / 220898679359) := by
    rw [show ((220898679359 / 125000000000) : ℝ) = ((125000000000 / 220898679359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (405435941 / 1000000000) ≤ -Real.log (250000000000 / 374989062691) ∧
    -Real.log (250000000000 / 374989062691) ≤ (202717971 / 500000000) := by
  have h := checkLog_sound (w := (124989062691 / 624989062691)) (n := 12)
    (lo := (405435941 / 1000000000)) (hi := (202717971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374989062691 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374989062691 / 250000000000) = 1/(250000000000 / 374989062691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (405435941 / 1000000000) (202717971 / 500000000) (Real.log (374989062691 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (374989062691 / 250000000000) = -Real.log (250000000000 / 374989062691) := by
    rw [show ((374989062691 / 250000000000) : ℝ) = ((250000000000 / 374989062691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (50762831 / 125000000) ≤ -Real.log (500000000000 / 750478307953) ∧
    -Real.log (500000000000 / 750478307953) ≤ (406102649 / 1000000000) := by
  have h := checkLog_sound (w := (250478307953 / 1250478307953)) (n := 12)
    (lo := (50762831 / 125000000)) (hi := (406102649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750478307953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750478307953 / 500000000000) = 1/(500000000000 / 750478307953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (50762831 / 125000000) (406102649 / 1000000000) (Real.log (750478307953 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (750478307953 / 500000000000) = -Real.log (500000000000 / 750478307953) := by
    rw [show ((750478307953 / 500000000000) : ℝ) = ((500000000000 / 750478307953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (51187 / 1250000) ≤ -Real.log (239969376591 / 250000000000) ∧
    -Real.log (239969376591 / 250000000000) ≤ (40949601 / 1000000000) := by
  have h := checkLog_sound (w := (10030623409 / 489969376591)) (n := 12)
    (lo := (51187 / 1250000)) (hi := (40949601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239969376591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239969376591) = 1/(239969376591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40949601 / 1000000000) (-51187 / 1250000) (Real.log (239969376591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40816161 / 1000000000) ≤ -Real.log (240001399951 / 250000000000) ∧
    -Real.log (240001399951 / 250000000000) ≤ (20408081 / 500000000) := by
  have h := checkLog_sound (w := (9998600049 / 490001399951)) (n := 12)
    (lo := (40816161 / 1000000000)) (hi := (20408081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240001399951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240001399951) = 1/(240001399951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20408081 / 500000000) (-40816161 / 1000000000) (Real.log (240001399951 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell237

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell238Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell238
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

theorem reflection_log_1_neg : (329331849 / 1000000000) ≤ -Real.log (5120 / 7117) ∧
    -Real.log (5120 / 7117) ≤ (6586637 / 20000000) := by
  have h := checkLog_sound (w := (1997 / 12237)) (n := 12)
    (lo := (329331849 / 1000000000)) (hi := (6586637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7117 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7117 / 5120) = 1/(5120 / 7117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (329331849 / 1000000000) (6586637 / 20000000) (Real.log (7117 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7117 / 5120) = -Real.log (5120 / 7117) := by
    rw [show ((7117 / 5120) : ℝ) = ((5120 / 7117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (12359009 / 25000000) ≤ -Real.log (3123 / 5120) ∧
    -Real.log (3123 / 5120) ≤ (494360361 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 8243)) (n := 12)
    (lo := (12359009 / 25000000)) (hi := (494360361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3123) = 1/(3123 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-494360361 / 1000000000) (-12359009 / 25000000) (Real.log (3123 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164455117 / 500000000) ≤ -Real.log (2560 / 3557) ∧
    -Real.log (2560 / 3557) ≤ (65782047 / 200000000) := by
  have h := checkLog_sound (w := (997 / 6117)) (n := 12)
    (lo := (164455117 / 500000000)) (hi := (65782047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3557 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3557 / 2560) = 1/(2560 / 3557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164455117 / 500000000) (65782047 / 200000000) (Real.log (3557 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3557 / 2560) = -Real.log (2560 / 3557) := by
    rw [show ((3557 / 2560) : ℝ) = ((2560 / 3557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (493400207 / 1000000000) ≤ -Real.log (1563 / 2560) ∧
    -Real.log (1563 / 2560) ≤ (30837513 / 62500000) := by
  have h := checkLog_sound (w := (997 / 4123)) (n := 12)
    (lo := (493400207 / 1000000000)) (hi := (30837513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1563) = 1/(1563 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30837513 / 62500000) (-493400207 / 1000000000) (Real.log (1563 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (244704631 / 1000000000) ≤ -Real.log (250000 / 319311) ∧
    -Real.log (250000 / 319311) ≤ (30588079 / 125000000) := by
  have h := checkLog_sound (w := (69311 / 569311)) (n := 12)
    (lo := (244704631 / 1000000000)) (hi := (30588079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319311 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319311 / 250000) = 1/(250000 / 319311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (244704631 / 1000000000) (30588079 / 125000000) (Real.log (319311 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (319311 / 250000) = -Real.log (250000 / 319311) := by
    rw [show ((319311 / 250000) : ℝ) = ((250000 / 319311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (81170899 / 250000000) ≤ -Real.log (180689 / 250000) ∧
    -Real.log (180689 / 250000) ≤ (324683597 / 1000000000) := by
  have h := checkLog_sound (w := (69311 / 430689)) (n := 12)
    (lo := (81170899 / 250000000)) (hi := (324683597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 180689) = 1/(180689 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-324683597 / 1000000000) (-81170899 / 250000000) (Real.log (180689 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (245036541 / 1000000000) ≤ -Real.log (250000 / 319417) ∧
    -Real.log (250000 / 319417) ≤ (122518271 / 500000000) := by
  have h := checkLog_sound (w := (69417 / 569417)) (n := 12)
    (lo := (245036541 / 1000000000)) (hi := (122518271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319417 / 250000) = 1/(250000 / 319417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (245036541 / 1000000000) (122518271 / 500000000) (Real.log (319417 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (319417 / 250000) = -Real.log (250000 / 319417) := by
    rw [show ((319417 / 250000) : ℝ) = ((250000 / 319417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325270411 / 1000000000) ≤ -Real.log (180583 / 250000) ∧
    -Real.log (180583 / 250000) ≤ (81317603 / 250000000) := by
  have h := checkLog_sound (w := (69417 / 430583)) (n := 12)
    (lo := (325270411 / 1000000000)) (hi := (81317603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 180583) = 1/(180583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-81317603 / 250000000) (-325270411 / 1000000000) (Real.log (180583 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182575691 / 1000000000) ≤ -Real.log (200000 / 240061) ∧
    -Real.log (200000 / 240061) ≤ (45643923 / 250000000) := by
  have h := checkLog_sound (w := (40061 / 440061)) (n := 12)
    (lo := (182575691 / 1000000000)) (hi := (45643923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240061 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240061 / 200000) = 1/(200000 / 240061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182575691 / 1000000000) (45643923 / 250000000) (Real.log (240061 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (240061 / 200000) = -Real.log (200000 / 240061) := by
    rw [show ((240061 / 200000) : ℝ) = ((200000 / 240061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111762437 / 500000000) ≤ -Real.log (159939 / 200000) ∧
    -Real.log (159939 / 200000) ≤ (1788199 / 8000000) := by
  have h := checkLog_sound (w := (40061 / 359939)) (n := 12)
    (lo := (111762437 / 500000000)) (hi := (1788199 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 159939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 159939) = 1/(159939 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1788199 / 8000000) (-111762437 / 500000000) (Real.log (159939 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91421127 / 500000000) ≤ -Real.log (1600 / 1921) ∧
    -Real.log (1600 / 1921) ≤ (36568451 / 200000000) := by
  have h := checkLog_sound (w := (321 / 3521)) (n := 12)
    (lo := (91421127 / 500000000)) (hi := (36568451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1600) = 1/(1600 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91421127 / 500000000) (36568451 / 200000000) (Real.log (1921 / 1600)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1921 / 1600) = -Real.log (1600 / 1921) := by
    rw [show ((1921 / 1600) : ℝ) = ((1600 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111962553 / 500000000) ≤ -Real.log (1279 / 1600) ∧
    -Real.log (1279 / 1600) ≤ (223925107 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 2879)) (n := 12)
    (lo := (111962553 / 500000000)) (hi := (223925107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 1279) = 1/(1279 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223925107 / 1000000000) (-111962553 / 500000000) (Real.log (1279 / 1600)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20557761 / 25000000) ≤ -Real.log (250000000000 / 568937939859) ∧
    -Real.log (250000000000 / 568937939859) ≤ (411155221 / 500000000) := by
  have h := checkLog_sound (w := (68937939859 / 1068937939859)) (n := 12)
    (lo := (6458163 / 50000000)) (hi := (129163261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568937939859 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568937939859 / 500000000000) = 1/(250000000000 / 568937939859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20557761 / 25000000) (411155221 / 500000000) (Real.log (568937939859 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (568937939859 / 250000000000) = -Real.log (250000000000 / 568937939859) := by
    rw [show ((568937939859 / 250000000000) : ℝ) = ((250000000000 / 568937939859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (823692209 / 1000000000) ≤ -Real.log (500000000000 / 1139449247519) ∧
    -Real.log (500000000000 / 1139449247519) ≤ (823692211 / 1000000000) := by
  have h := checkLog_sound (w := (139449247519 / 2139449247519)) (n := 12)
    (lo := (130545029 / 1000000000)) (hi := (13054503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139449247519 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1139449247519 / 1000000000000) = 1/(500000000000 / 1139449247519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (823692209 / 1000000000) (823692211 / 1000000000) (Real.log (1139449247519 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1139449247519 / 500000000000) = -Real.log (500000000000 / 1139449247519) := by
    rw [show ((1139449247519 / 500000000000) : ℝ) = ((500000000000 / 1139449247519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (142347057 / 250000000) ≤ -Real.log (500000000000 / 883592803103) ∧
    -Real.log (500000000000 / 883592803103) ≤ (569388229 / 1000000000) := by
  have h := checkLog_sound (w := (383592803103 / 1383592803103)) (n := 12)
    (lo := (142347057 / 250000000)) (hi := (569388229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883592803103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(883592803103 / 500000000000) = 1/(500000000000 / 883592803103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142347057 / 250000000) (569388229 / 1000000000) (Real.log (883592803103 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (883592803103 / 500000000000) = -Real.log (500000000000 / 883592803103) := by
    rw [show ((883592803103 / 500000000000) : ℝ) = ((500000000000 / 883592803103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (570306953 / 1000000000) ≤ -Real.log (500000000000 / 884404955063) ∧
    -Real.log (500000000000 / 884404955063) ≤ (285153477 / 500000000) := by
  have h := checkLog_sound (w := (384404955063 / 1384404955063)) (n := 12)
    (lo := (570306953 / 1000000000)) (hi := (285153477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884404955063 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884404955063 / 500000000000) = 1/(500000000000 / 884404955063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (570306953 / 1000000000) (285153477 / 500000000) (Real.log (884404955063 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (884404955063 / 500000000000) = -Real.log (500000000000 / 884404955063) := by
    rw [show ((884404955063 / 500000000000) : ℝ) = ((500000000000 / 884404955063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (81220113 / 200000000) ≤ -Real.log (250000000000 / 375238372129) ∧
    -Real.log (250000000000 / 375238372129) ≤ (203050283 / 500000000) := by
  have h := checkLog_sound (w := (125238372129 / 625238372129)) (n := 12)
    (lo := (81220113 / 200000000)) (hi := (203050283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375238372129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375238372129 / 250000000000) = 1/(250000000000 / 375238372129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81220113 / 200000000) (203050283 / 500000000) (Real.log (375238372129 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (375238372129 / 250000000000) = -Real.log (250000000000 / 375238372129) := by
    rw [show ((375238372129 / 250000000000) : ℝ) = ((250000000000 / 375238372129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406767361 / 1000000000) ≤ -Real.log (125000000000 / 187744331509) ∧
    -Real.log (125000000000 / 187744331509) ≤ (203383681 / 500000000) := by
  have h := checkLog_sound (w := (62744331509 / 312744331509)) (n := 12)
    (lo := (406767361 / 1000000000)) (hi := (203383681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187744331509 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187744331509 / 125000000000) = 1/(125000000000 / 187744331509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406767361 / 1000000000) (203383681 / 500000000) (Real.log (187744331509 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (187744331509 / 125000000000) = -Real.log (125000000000 / 187744331509) := by
    rw [show ((187744331509 / 125000000000) : ℝ) = ((125000000000 / 187744331509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10270713 / 250000000) ≤ -Real.log (2456959 / 2560000) ∧
    -Real.log (2456959 / 2560000) ≤ (41082853 / 1000000000) := by
  have h := checkLog_sound (w := (103041 / 5016959)) (n := 12)
    (lo := (10270713 / 250000000)) (hi := (41082853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 2456959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 2456959) = 1/(2456959 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41082853 / 1000000000) (-10270713 / 250000000) (Real.log (2456959 / 2560000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20474591 / 500000000) ≤ -Real.log (38395116279 / 40000000000) ∧
    -Real.log (38395116279 / 40000000000) ≤ (40949183 / 1000000000) := by
  have h := checkLog_sound (w := (1604883721 / 78395116279)) (n := 12)
    (lo := (20474591 / 500000000)) (hi := (40949183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38395116279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38395116279) = 1/(38395116279 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-40949183 / 1000000000) (-20474591 / 500000000) (Real.log (38395116279 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell238

end


