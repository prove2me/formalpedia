-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0186Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0186Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:17:57.917823+00:00
-- url     : https://prove2.me/theorems/d0dbe098-d4ee-4dc7-807d-3239c915537d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0186Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0187Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0186Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0187Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0191Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0186Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0187Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0191Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0186Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0187Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0191Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0186Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0187Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0188Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0189Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0190Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0191Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0186Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0186
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

theorem reflection_log_1_neg : (54386743 / 200000000) ≤ -Real.log (16 / 21) ∧
    -Real.log (16 / 21) ≤ (67983429 / 250000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 16) = 1/(16 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54386743 / 200000000) (67983429 / 250000000) (Real.log (21 / 16)) := by
  have h := reflection_log_1_neg
  have he : Real.log (21 / 16) = -Real.log (16 / 21) := by
    rw [show ((21 / 16) : ℝ) = ((16 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (374693449 / 1000000000) ≤ -Real.log (11 / 16) ∧
    -Real.log (11 / 16) ≤ (7493869 / 20000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 11) = 1/(11 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7493869 / 20000000) (-374693449 / 1000000000) (Real.log (11 / 16)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (271487187 / 1000000000) ≤ -Real.log (5120 / 6717) ∧
    -Real.log (5120 / 6717) ≤ (67871797 / 250000000) := by
  have h := checkLog_sound (w := (1597 / 11837)) (n := 12)
    (lo := (271487187 / 1000000000)) (hi := (67871797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6717 / 5120) = 1/(5120 / 6717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (271487187 / 1000000000) (67871797 / 250000000) (Real.log (6717 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6717 / 5120) = -Real.log (5120 / 6717) := by
    rw [show ((6717 / 5120) : ℝ) = ((5120 / 6717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (373841539 / 1000000000) ≤ -Real.log (3523 / 5120) ∧
    -Real.log (3523 / 5120) ≤ (18692077 / 50000000) := by
  have h := checkLog_sound (w := (1597 / 8643)) (n := 12)
    (lo := (373841539 / 1000000000)) (hi := (18692077 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3523) = 1/(3523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18692077 / 50000000) (-373841539 / 1000000000) (Real.log (3523 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97101563 / 200000000) ≤ -Real.log (8 / 13) ∧
    -Real.log (8 / 13) ≤ (60688477 / 125000000) := by
  have h := checkLog_sound (w := (5 / 21)) (n := 12)
    (lo := (97101563 / 200000000)) (hi := (60688477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 8) = 1/(8 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97101563 / 200000000) (60688477 / 125000000) (Real.log (13 / 8)) := by
  have h := reflection_log_5_neg
  have he : Real.log (13 / 8) = -Real.log (8 / 13) := by
    rw [show ((13 / 8) : ℝ) = ((8 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245207313 / 250000000) ≤ -Real.log (3 / 8) ∧
    -Real.log (3 / 8) ≤ (490414627 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4 / 3) = 1/(3 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-490414627 / 500000000) (-245207313 / 250000000) (Real.log (3 / 8)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (484786401 / 1000000000) ≤ -Real.log (2560 / 4157) ∧
    -Real.log (2560 / 4157) ≤ (242393201 / 500000000) := by
  have h := checkLog_sound (w := (1597 / 6717)) (n := 12)
    (lo := (484786401 / 1000000000)) (hi := (242393201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4157 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4157 / 2560) = 1/(2560 / 4157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (484786401 / 1000000000) (242393201 / 500000000) (Real.log (4157 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4157 / 2560) = -Real.log (2560 / 4157) := by
    rw [show ((4157 / 2560) : ℝ) = ((2560 / 4157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (7821673 / 8000000) ≤ -Real.log (963 / 2560) ∧
    -Real.log (963 / 2560) ≤ (977709127 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 2243)) (n := 12)
    (lo := (56912389 / 200000000)) (hi := (142280973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 963) = 1/(963 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-977709127 / 1000000000) (-7821673 / 8000000) (Real.log (963 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (23211773 / 62500000) ≤ -Real.log (500000 / 724873) ∧
    -Real.log (500000 / 724873) ≤ (371388369 / 1000000000) := by
  have h := checkLog_sound (w := (224873 / 1224873)) (n := 12)
    (lo := (23211773 / 62500000)) (hi := (371388369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724873 / 500000) = 1/(500000 / 724873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (23211773 / 62500000) (371388369 / 1000000000) (Real.log (724873 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (724873 / 500000) = -Real.log (500000 / 724873) := by
    rw [show ((724873 / 500000) : ℝ) = ((500000 / 724873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (597375289 / 1000000000) ≤ -Real.log (275127 / 500000) ∧
    -Real.log (275127 / 500000) ≤ (59737529 / 100000000) := by
  have h := checkLog_sound (w := (224873 / 775127)) (n := 12)
    (lo := (597375289 / 1000000000)) (hi := (59737529 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 275127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 275127) = 1/(275127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-59737529 / 100000000) (-597375289 / 1000000000) (Real.log (275127 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (371999323 / 1000000000) ≤ -Real.log (125000 / 181329) ∧
    -Real.log (125000 / 181329) ≤ (92999831 / 250000000) := by
  have h := checkLog_sound (w := (56329 / 306329)) (n := 12)
    (lo := (371999323 / 1000000000)) (hi := (92999831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181329 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181329 / 125000) = 1/(125000 / 181329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (371999323 / 1000000000) (92999831 / 250000000) (Real.log (181329 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (181329 / 125000) = -Real.log (125000 / 181329) := by
    rw [show ((181329 / 125000) : ℝ) = ((125000 / 181329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1169896 / 1953125) ≤ -Real.log (68671 / 125000) ∧
    -Real.log (68671 / 125000) ≤ (598986753 / 1000000000) := by
  have h := checkLog_sound (w := (56329 / 193671)) (n := 12)
    (lo := (1169896 / 1953125)) (hi := (598986753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 68671) = 1/(68671 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-598986753 / 1000000000) (-1169896 / 1953125) (Real.log (68671 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (290304131 / 1000000000) ≤ -Real.log (500000 / 668417) ∧
    -Real.log (500000 / 668417) ≤ (72576033 / 250000000) := by
  have h := checkLog_sound (w := (168417 / 1168417)) (n := 12)
    (lo := (290304131 / 1000000000)) (hi := (72576033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668417 / 500000) = 1/(500000 / 668417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (290304131 / 1000000000) (72576033 / 250000000) (Real.log (668417 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (668417 / 500000) = -Real.log (500000 / 668417) := by
    rw [show ((668417 / 500000) : ℝ) = ((500000 / 668417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (410729943 / 1000000000) ≤ -Real.log (331583 / 500000) ∧
    -Real.log (331583 / 500000) ≤ (51341243 / 125000000) := by
  have h := checkLog_sound (w := (168417 / 831583)) (n := 12)
    (lo := (410729943 / 1000000000)) (hi := (51341243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331583) = 1/(331583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-51341243 / 125000000) (-410729943 / 1000000000) (Real.log (331583 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14542951 / 50000000) ≤ -Real.log (125000 / 167197) ∧
    -Real.log (125000 / 167197) ≤ (290859021 / 1000000000) := by
  have h := checkLog_sound (w := (42197 / 292197)) (n := 12)
    (lo := (14542951 / 50000000)) (hi := (290859021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167197 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167197 / 125000) = 1/(125000 / 167197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14542951 / 50000000) (290859021 / 1000000000) (Real.log (167197 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (167197 / 125000) = -Real.log (125000 / 167197) := by
    rw [show ((167197 / 125000) : ℝ) = ((125000 / 167197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102962361 / 250000000) ≤ -Real.log (82803 / 125000) ∧
    -Real.log (82803 / 125000) ≤ (82369889 / 200000000) := by
  have h := checkLog_sound (w := (42197 / 207803)) (n := 12)
    (lo := (102962361 / 250000000)) (hi := (82369889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 82803) = 1/(82803 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-82369889 / 200000000) (-102962361 / 250000000) (Real.log (82803 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (968763657 / 1000000000) ≤ -Real.log (100000000000 / 263468507271) ∧
    -Real.log (100000000000 / 263468507271) ≤ (968763659 / 1000000000) := by
  have h := checkLog_sound (w := (63468507271 / 463468507271)) (n := 12)
    (lo := (275616477 / 1000000000)) (hi := (137808239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263468507271 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263468507271 / 200000000000) = 1/(100000000000 / 263468507271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (968763657 / 1000000000) (968763659 / 1000000000) (Real.log (263468507271 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (263468507271 / 100000000000) = -Real.log (100000000000 / 263468507271) := by
    rw [show ((263468507271 / 100000000000) : ℝ) = ((100000000000 / 263468507271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38839443 / 40000000) ≤ -Real.log (1953125000 / 5157318273) ∧
    -Real.log (1953125000 / 5157318273) ≤ (970986077 / 1000000000) := by
  have h := checkLog_sound (w := (1251068273 / 9063568273)) (n := 12)
    (lo := (55567779 / 200000000)) (hi := (17364931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5157318273 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5157318273 / 3906250000) = 1/(1953125000 / 5157318273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38839443 / 40000000) (970986077 / 1000000000) (Real.log (5157318273 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5157318273 / 1953125000) = -Real.log (1953125000 / 5157318273) := by
    rw [show ((5157318273 / 1953125000) : ℝ) = ((1953125000 / 5157318273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (350517037 / 500000000) ≤ -Real.log (250000000000 / 503959038913) ∧
    -Real.log (250000000000 / 503959038913) ≤ (175258519 / 250000000) := by
  have h := checkLog_sound (w := (3959038913 / 1003959038913)) (n := 12)
    (lo := (3943447 / 500000000)) (hi := (1577379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503959038913 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(503959038913 / 500000000000) = 1/(250000000000 / 503959038913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (350517037 / 500000000) (175258519 / 250000000) (Real.log (503959038913 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (503959038913 / 250000000000) = -Real.log (250000000000 / 503959038913) := by
    rw [show ((503959038913 / 250000000000) : ℝ) = ((250000000000 / 503959038913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (43919279 / 62500000) ≤ -Real.log (250000000000 / 504803569919) ∧
    -Real.log (250000000000 / 504803569919) ≤ (351354233 / 500000000) := by
  have h := checkLog_sound (w := (4803569919 / 1004803569919)) (n := 12)
    (lo := (2390321 / 250000000)) (hi := (1912257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((504803569919 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(504803569919 / 500000000000) = 1/(250000000000 / 504803569919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (43919279 / 62500000) (351354233 / 500000000) (Real.log (504803569919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (504803569919 / 250000000000) = -Real.log (250000000000 / 504803569919) := by
    rw [show ((504803569919 / 250000000000) : ℝ) = ((250000000000 / 504803569919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0186

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0187Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0187
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

theorem reflection_log_1_neg : (271487187 / 1000000000) ≤ -Real.log (5120 / 6717) ∧
    -Real.log (5120 / 6717) ≤ (67871797 / 250000000) := by
  have h := checkLog_sound (w := (1597 / 11837)) (n := 12)
    (lo := (271487187 / 1000000000)) (hi := (67871797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6717 / 5120) = 1/(5120 / 6717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (271487187 / 1000000000) (67871797 / 250000000) (Real.log (6717 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6717 / 5120) = -Real.log (5120 / 6717) := by
    rw [show ((6717 / 5120) : ℝ) = ((5120 / 6717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (373841539 / 1000000000) ≤ -Real.log (3523 / 5120) ∧
    -Real.log (3523 / 5120) ≤ (18692077 / 50000000) := by
  have h := checkLog_sound (w := (1597 / 8643)) (n := 12)
    (lo := (373841539 / 1000000000)) (hi := (18692077 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3523) = 1/(3523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18692077 / 50000000) (-373841539 / 1000000000) (Real.log (3523 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (271040459 / 1000000000) ≤ -Real.log (2560 / 3357) ∧
    -Real.log (2560 / 3357) ≤ (13552023 / 50000000) := by
  have h := checkLog_sound (w := (797 / 5917)) (n := 12)
    (lo := (271040459 / 1000000000)) (hi := (13552023 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3357 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3357 / 2560) = 1/(2560 / 3357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (271040459 / 1000000000) (13552023 / 50000000) (Real.log (3357 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3357 / 2560) = -Real.log (2560 / 3357) := by
    rw [show ((3357 / 2560) : ℝ) = ((2560 / 3357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74598071 / 200000000) ≤ -Real.log (1763 / 2560) ∧
    -Real.log (1763 / 2560) ≤ (93247589 / 250000000) := by
  have h := checkLog_sound (w := (797 / 4323)) (n := 12)
    (lo := (74598071 / 200000000)) (hi := (93247589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1763) = 1/(1763 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-93247589 / 250000000) (-74598071 / 200000000) (Real.log (1763 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (484786401 / 1000000000) ≤ -Real.log (2560 / 4157) ∧
    -Real.log (2560 / 4157) ≤ (242393201 / 500000000) := by
  have h := checkLog_sound (w := (1597 / 6717)) (n := 12)
    (lo := (484786401 / 1000000000)) (hi := (242393201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4157 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4157 / 2560) = 1/(2560 / 4157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (484786401 / 1000000000) (242393201 / 500000000) (Real.log (4157 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4157 / 2560) = -Real.log (2560 / 4157) := by
    rw [show ((4157 / 2560) : ℝ) = ((2560 / 4157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7821673 / 8000000) ≤ -Real.log (963 / 2560) ∧
    -Real.log (963 / 2560) ≤ (977709127 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 2243)) (n := 12)
    (lo := (56912389 / 200000000)) (hi := (142280973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 963) = 1/(963 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-977709127 / 1000000000) (-7821673 / 8000000) (Real.log (963 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (242032233 / 500000000) ≤ -Real.log (1280 / 2077) ∧
    -Real.log (1280 / 2077) ≤ (484064467 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 3357)) (n := 12)
    (lo := (242032233 / 500000000)) (hi := (484064467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2077 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2077 / 1280) = 1/(1280 / 2077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (242032233 / 500000000) (484064467 / 1000000000) (Real.log (2077 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2077 / 1280) = -Real.log (1280 / 2077) := by
    rw [show ((2077 / 1280) : ℝ) = ((1280 / 2077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (487299351 / 500000000) ≤ -Real.log (483 / 1280) ∧
    -Real.log (483 / 1280) ≤ (60912419 / 62500000) := by
  have h := checkLog_sound (w := (157 / 1123)) (n := 12)
    (lo := (140725761 / 500000000)) (hi := (281451523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 483) = 1/(483 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-60912419 / 62500000) (-487299351 / 500000000) (Real.log (483 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18538921 / 50000000) ≤ -Real.log (500000 / 724431) ∧
    -Real.log (500000 / 724431) ≤ (370778421 / 1000000000) := by
  have h := checkLog_sound (w := (224431 / 1224431)) (n := 12)
    (lo := (18538921 / 50000000)) (hi := (370778421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724431 / 500000) = 1/(500000 / 724431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18538921 / 50000000) (370778421 / 1000000000) (Real.log (724431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (724431 / 500000) = -Real.log (500000 / 724431) := by
    rw [show ((724431 / 500000) : ℝ) = ((500000 / 724431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (595770047 / 1000000000) ≤ -Real.log (275569 / 500000) ∧
    -Real.log (275569 / 500000) ≤ (9308907 / 15625000) := by
  have h := checkLog_sound (w := (224431 / 775569)) (n := 12)
    (lo := (595770047 / 1000000000)) (hi := (9308907 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 275569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 275569) = 1/(275569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9308907 / 15625000) (-595770047 / 1000000000) (Real.log (275569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (185694529 / 500000000) ≤ -Real.log (1000000 / 1449747) ∧
    -Real.log (1000000 / 1449747) ≤ (371389059 / 1000000000) := by
  have h := checkLog_sound (w := (449747 / 2449747)) (n := 12)
    (lo := (185694529 / 500000000)) (hi := (371389059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449747 / 1000000) = 1/(1000000 / 1449747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (185694529 / 500000000) (371389059 / 1000000000) (Real.log (1449747 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1449747 / 1000000) = -Real.log (1000000 / 1449747) := by
    rw [show ((1449747 / 1000000) : ℝ) = ((1000000 / 1449747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (298688553 / 500000000) ≤ -Real.log (550253 / 1000000) ∧
    -Real.log (550253 / 1000000) ≤ (597377107 / 1000000000) := by
  have h := checkLog_sound (w := (449747 / 1550253)) (n := 12)
    (lo := (298688553 / 500000000)) (hi := (597377107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 550253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 550253) = 1/(550253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-597377107 / 1000000000) (-298688553 / 500000000) (Real.log (550253 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (289750431 / 1000000000) ≤ -Real.log (500000 / 668047) ∧
    -Real.log (500000 / 668047) ≤ (9054701 / 31250000) := by
  have h := checkLog_sound (w := (168047 / 1168047)) (n := 12)
    (lo := (289750431 / 1000000000)) (hi := (9054701 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668047 / 500000) = 1/(500000 / 668047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (289750431 / 1000000000) (9054701 / 31250000) (Real.log (668047 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (668047 / 500000) = -Real.log (500000 / 668047) := by
    rw [show ((668047 / 500000) : ℝ) = ((500000 / 668047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (81922941 / 200000000) ≤ -Real.log (331953 / 500000) ∧
    -Real.log (331953 / 500000) ≤ (204807353 / 500000000) := by
  have h := checkLog_sound (w := (168047 / 831953)) (n := 12)
    (lo := (81922941 / 200000000)) (hi := (204807353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331953) = 1/(331953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-204807353 / 500000000) (-81922941 / 200000000) (Real.log (331953 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (290304879 / 1000000000) ≤ -Real.log (200000 / 267367) ∧
    -Real.log (200000 / 267367) ≤ (3628811 / 12500000) := by
  have h := checkLog_sound (w := (67367 / 467367)) (n := 12)
    (lo := (290304879 / 1000000000)) (hi := (3628811 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267367 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267367 / 200000) = 1/(200000 / 267367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (290304879 / 1000000000) (3628811 / 12500000) (Real.log (267367 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (267367 / 200000) = -Real.log (200000 / 267367) := by
    rw [show ((267367 / 200000) : ℝ) = ((200000 / 267367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (8214629 / 20000000) ≤ -Real.log (132633 / 200000) ∧
    -Real.log (132633 / 200000) ≤ (410731451 / 1000000000) := by
  have h := checkLog_sound (w := (67367 / 332633)) (n := 12)
    (lo := (8214629 / 20000000)) (hi := (410731451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132633) = 1/(132633 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-410731451 / 1000000000) (-8214629 / 20000000) (Real.log (132633 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (966548467 / 1000000000) ≤ -Real.log (125000000000 / 328606900631) ∧
    -Real.log (125000000000 / 328606900631) ≤ (966548469 / 1000000000) := by
  have h := checkLog_sound (w := (78606900631 / 578606900631)) (n := 12)
    (lo := (273401287 / 1000000000)) (hi := (34175161 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328606900631 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328606900631 / 250000000000) = 1/(125000000000 / 328606900631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (966548467 / 1000000000) (966548469 / 1000000000) (Real.log (328606900631 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (328606900631 / 125000000000) = -Real.log (125000000000 / 328606900631) := by
    rw [show ((328606900631 / 125000000000) : ℝ) = ((125000000000 / 328606900631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (242191541 / 250000000) ≤ -Real.log (62500000000 / 164668229887) ∧
    -Real.log (62500000000 / 164668229887) ≤ (484383083 / 500000000) := by
  have h := checkLog_sound (w := (39668229887 / 289668229887)) (n := 12)
    (lo := (34452373 / 125000000)) (hi := (55123797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164668229887 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(164668229887 / 125000000000) = 1/(62500000000 / 164668229887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (242191541 / 250000000) (484383083 / 500000000) (Real.log (164668229887 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164668229887 / 62500000000) = -Real.log (62500000000 / 164668229887) := by
    rw [show ((164668229887 / 62500000000) : ℝ) = ((62500000000 / 164668229887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (699365137 / 1000000000) ≤ -Real.log (250000000000 / 503118664389) ∧
    -Real.log (250000000000 / 503118664389) ≤ (699365139 / 1000000000) := by
  have h := checkLog_sound (w := (3118664389 / 1003118664389)) (n := 12)
    (lo := (6217957 / 1000000000)) (hi := (3108979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503118664389 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(503118664389 / 500000000000) = 1/(250000000000 / 503118664389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (699365137 / 1000000000) (699365139 / 1000000000) (Real.log (503118664389 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (503118664389 / 250000000000) = -Real.log (250000000000 / 503118664389) := by
    rw [show ((503118664389 / 250000000000) : ℝ) = ((250000000000 / 503118664389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (70103633 / 100000000) ≤ -Real.log (15625000000 / 31497510989) ∧
    -Real.log (15625000000 / 31497510989) ≤ (175259083 / 250000000) := by
  have h := checkLog_sound (w := (247510989 / 62747510989)) (n := 12)
    (lo := (157783 / 20000000)) (hi := (7889151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31497510989 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31497510989 / 31250000000) = 1/(15625000000 / 31497510989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (70103633 / 100000000) (175259083 / 250000000) (Real.log (31497510989 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31497510989 / 15625000000) = -Real.log (15625000000 / 31497510989) := by
    rw [show ((31497510989 / 15625000000) : ℝ) = ((15625000000 / 31497510989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0187

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0188Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0188
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

theorem reflection_log_1_neg : (271040459 / 1000000000) ≤ -Real.log (2560 / 3357) ∧
    -Real.log (2560 / 3357) ≤ (13552023 / 50000000) := by
  have h := checkLog_sound (w := (797 / 5917)) (n := 12)
    (lo := (271040459 / 1000000000)) (hi := (13552023 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3357 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3357 / 2560) = 1/(2560 / 3357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (271040459 / 1000000000) (13552023 / 50000000) (Real.log (3357 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3357 / 2560) = -Real.log (2560 / 3357) := by
    rw [show ((3357 / 2560) : ℝ) = ((2560 / 3357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74598071 / 200000000) ≤ -Real.log (1763 / 2560) ∧
    -Real.log (1763 / 2560) ≤ (93247589 / 250000000) := by
  have h := checkLog_sound (w := (797 / 4323)) (n := 12)
    (lo := (74598071 / 200000000)) (hi := (93247589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1763) = 1/(1763 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-93247589 / 250000000) (-74598071 / 200000000) (Real.log (1763 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67648383 / 250000000) ≤ -Real.log (5120 / 6711) ∧
    -Real.log (5120 / 6711) ≤ (270593533 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 11831)) (n := 12)
    (lo := (67648383 / 250000000)) (hi := (270593533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6711 / 5120) = 1/(5120 / 6711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67648383 / 250000000) (270593533 / 1000000000) (Real.log (6711 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6711 / 5120) = -Real.log (5120 / 6711) := by
    rw [show ((6711 / 5120) : ℝ) = ((5120 / 6711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (186069947 / 500000000) ≤ -Real.log (3529 / 5120) ∧
    -Real.log (3529 / 5120) ≤ (74427979 / 200000000) := by
  have h := checkLog_sound (w := (1591 / 8649)) (n := 12)
    (lo := (186069947 / 500000000)) (hi := (74427979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3529) = 1/(3529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-74427979 / 200000000) (-186069947 / 500000000) (Real.log (3529 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242032233 / 500000000) ≤ -Real.log (1280 / 2077) ∧
    -Real.log (1280 / 2077) ≤ (484064467 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 3357)) (n := 12)
    (lo := (242032233 / 500000000)) (hi := (484064467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2077 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2077 / 1280) = 1/(1280 / 2077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242032233 / 500000000) (484064467 / 1000000000) (Real.log (2077 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2077 / 1280) = -Real.log (1280 / 2077) := by
    rw [show ((2077 / 1280) : ℝ) = ((1280 / 2077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (487299351 / 500000000) ≤ -Real.log (483 / 1280) ∧
    -Real.log (483 / 1280) ≤ (60912419 / 62500000) := by
  have h := checkLog_sound (w := (157 / 1123)) (n := 12)
    (lo := (140725761 / 500000000)) (hi := (281451523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 483) = 1/(483 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60912419 / 62500000) (-487299351 / 500000000) (Real.log (483 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48334201 / 100000000) ≤ -Real.log (2560 / 4151) ∧
    -Real.log (2560 / 4151) ≤ (483342011 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 6711)) (n := 12)
    (lo := (48334201 / 100000000)) (hi := (483342011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4151 / 2560) = 1/(2560 / 4151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48334201 / 100000000) (483342011 / 1000000000) (Real.log (4151 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4151 / 2560) = -Real.log (2560 / 4151) := by
    rw [show ((4151 / 2560) : ℝ) = ((2560 / 4151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (38859917 / 40000000) ≤ -Real.log (969 / 2560) ∧
    -Real.log (969 / 2560) ≤ (971497927 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 2249)) (n := 12)
    (lo := (55670149 / 200000000)) (hi := (139175373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 969) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 969) = 1/(969 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-971497927 / 1000000000) (-38859917 / 40000000) (Real.log (969 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3701681 / 10000000) ≤ -Real.log (500000 / 723989) ∧
    -Real.log (500000 / 723989) ≤ (370168101 / 1000000000) := by
  have h := checkLog_sound (w := (223989 / 1223989)) (n := 12)
    (lo := (3701681 / 10000000)) (hi := (370168101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723989 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723989 / 500000) = 1/(500000 / 723989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3701681 / 10000000) (370168101 / 1000000000) (Real.log (723989 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (723989 / 500000) = -Real.log (500000 / 723989) := by
    rw [show ((723989 / 500000) : ℝ) = ((500000 / 723989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (297083689 / 500000000) ≤ -Real.log (276011 / 500000) ∧
    -Real.log (276011 / 500000) ≤ (594167379 / 1000000000) := by
  have h := checkLog_sound (w := (223989 / 776011)) (n := 12)
    (lo := (297083689 / 500000000)) (hi := (594167379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276011) = 1/(276011 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-594167379 / 1000000000) (-297083689 / 500000000) (Real.log (276011 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37077911 / 100000000) ≤ -Real.log (1000000 / 1448863) ∧
    -Real.log (1000000 / 1448863) ≤ (370779111 / 1000000000) := by
  have h := checkLog_sound (w := (448863 / 2448863)) (n := 12)
    (lo := (37077911 / 100000000)) (hi := (370779111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1448863 / 1000000) = 1/(1000000 / 1448863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37077911 / 100000000) (370779111 / 1000000000) (Real.log (1448863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1448863 / 1000000) = -Real.log (1000000 / 1448863) := by
    rw [show ((1448863 / 1000000) : ℝ) = ((1000000 / 1448863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (595771861 / 1000000000) ≤ -Real.log (551137 / 1000000) ∧
    -Real.log (551137 / 1000000) ≤ (297885931 / 500000000) := by
  have h := checkLog_sound (w := (448863 / 1551137)) (n := 12)
    (lo := (595771861 / 1000000000)) (hi := (297885931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 551137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 551137) = 1/(551137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-297885931 / 500000000) (-595771861 / 1000000000) (Real.log (551137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144598587 / 500000000) ≤ -Real.log (200000 / 267071) ∧
    -Real.log (200000 / 267071) ≤ (11567887 / 40000000) := by
  have h := checkLog_sound (w := (67071 / 467071)) (n := 12)
    (lo := (144598587 / 500000000)) (hi := (11567887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267071 / 200000) = 1/(200000 / 267071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144598587 / 500000000) (11567887 / 40000000) (Real.log (267071 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (267071 / 200000) = -Real.log (200000 / 267071) := by
    rw [show ((267071 / 200000) : ℝ) = ((200000 / 267071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (81700443 / 200000000) ≤ -Real.log (132929 / 200000) ∧
    -Real.log (132929 / 200000) ≤ (51062777 / 125000000) := by
  have h := checkLog_sound (w := (67071 / 332929)) (n := 12)
    (lo := (81700443 / 200000000)) (hi := (51062777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132929) = 1/(132929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-51062777 / 125000000) (-81700443 / 200000000) (Real.log (132929 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14487559 / 50000000) ≤ -Real.log (200000 / 267219) ∧
    -Real.log (200000 / 267219) ≤ (289751181 / 1000000000) := by
  have h := checkLog_sound (w := (67219 / 467219)) (n := 12)
    (lo := (14487559 / 50000000)) (hi := (289751181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267219 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267219 / 200000) = 1/(200000 / 267219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14487559 / 50000000) (289751181 / 1000000000) (Real.log (267219 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (267219 / 200000) = -Real.log (200000 / 267219) := by
    rw [show ((267219 / 200000) : ℝ) = ((200000 / 267219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102404053 / 250000000) ≤ -Real.log (132781 / 200000) ∧
    -Real.log (132781 / 200000) ≤ (409616213 / 1000000000) := by
  have h := checkLog_sound (w := (67219 / 332781)) (n := 12)
    (lo := (102404053 / 250000000)) (hi := (409616213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132781) = 1/(132781 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-409616213 / 1000000000) (-102404053 / 250000000) (Real.log (132781 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (482167739 / 500000000) ≤ -Real.log (500000000000 / 1311522004557) ∧
    -Real.log (500000000000 / 1311522004557) ≤ (24108387 / 25000000) := by
  have h := checkLog_sound (w := (311522004557 / 2311522004557)) (n := 12)
    (lo := (135594149 / 500000000)) (hi := (271188299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311522004557 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1311522004557 / 1000000000000) = 1/(500000000000 / 1311522004557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (482167739 / 500000000) (24108387 / 25000000) (Real.log (1311522004557 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1311522004557 / 500000000000) = -Real.log (500000000000 / 1311522004557) := by
    rw [show ((1311522004557 / 500000000000) : ℝ) = ((500000000000 / 1311522004557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (241637743 / 250000000) ≤ -Real.log (250000000000 / 657215447339) ∧
    -Real.log (250000000000 / 657215447339) ≤ (483275487 / 500000000) := by
  have h := checkLog_sound (w := (157215447339 / 1157215447339)) (n := 12)
    (lo := (17087737 / 62500000)) (hi := (273403793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657215447339 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(657215447339 / 500000000000) = 1/(250000000000 / 657215447339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (241637743 / 250000000) (483275487 / 500000000) (Real.log (657215447339 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (657215447339 / 250000000000) = -Real.log (250000000000 / 657215447339) := by
    rw [show ((657215447339 / 250000000000) : ℝ) = ((250000000000 / 657215447339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (174424847 / 250000000) ≤ -Real.log (250000000000 / 502281293021) ∧
    -Real.log (250000000000 / 502281293021) ≤ (69769939 / 100000000) := by
  have h := checkLog_sound (w := (2281293021 / 1002281293021)) (n := 12)
    (lo := (284513 / 62500000)) (hi := (4552209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502281293021 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(502281293021 / 500000000000) = 1/(250000000000 / 502281293021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (174424847 / 250000000) (69769939 / 100000000) (Real.log (502281293021 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (502281293021 / 250000000000) = -Real.log (250000000000 / 502281293021) := by
    rw [show ((502281293021 / 250000000000) : ℝ) = ((250000000000 / 502281293021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (699367391 / 1000000000) ≤ -Real.log (500000000000 / 1006239597533) ∧
    -Real.log (500000000000 / 1006239597533) ≤ (699367393 / 1000000000) := by
  have h := checkLog_sound (w := (6239597533 / 2006239597533)) (n := 12)
    (lo := (6220211 / 1000000000)) (hi := (1555053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006239597533 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006239597533 / 1000000000000) = 1/(500000000000 / 1006239597533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (699367391 / 1000000000) (699367393 / 1000000000) (Real.log (1006239597533 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1006239597533 / 500000000000) = -Real.log (500000000000 / 1006239597533) := by
    rw [show ((1006239597533 / 500000000000) : ℝ) = ((500000000000 / 1006239597533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0188

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0189Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0189
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

theorem reflection_log_1_neg : (67648383 / 250000000) ≤ -Real.log (5120 / 6711) ∧
    -Real.log (5120 / 6711) ≤ (270593533 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 11831)) (n := 12)
    (lo := (67648383 / 250000000)) (hi := (270593533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6711 / 5120) = 1/(5120 / 6711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67648383 / 250000000) (270593533 / 1000000000) (Real.log (6711 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6711 / 5120) = -Real.log (5120 / 6711) := by
    rw [show ((6711 / 5120) : ℝ) = ((5120 / 6711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (186069947 / 500000000) ≤ -Real.log (3529 / 5120) ∧
    -Real.log (3529 / 5120) ≤ (74427979 / 200000000) := by
  have h := checkLog_sound (w := (1591 / 8649)) (n := 12)
    (lo := (186069947 / 500000000)) (hi := (74427979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3529) = 1/(3529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-74427979 / 200000000) (-186069947 / 500000000) (Real.log (3529 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67536601 / 250000000) ≤ -Real.log (1280 / 1677) ∧
    -Real.log (1280 / 1677) ≤ (54029281 / 200000000) := by
  have h := checkLog_sound (w := (397 / 2957)) (n := 12)
    (lo := (67536601 / 250000000)) (hi := (54029281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1280) = 1/(1280 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67536601 / 250000000) (54029281 / 200000000) (Real.log (1677 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1677 / 1280) = -Real.log (1280 / 1677) := by
    rw [show ((1677 / 1280) : ℝ) = ((1280 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92822539 / 250000000) ≤ -Real.log (883 / 1280) ∧
    -Real.log (883 / 1280) ≤ (371290157 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2163)) (n := 12)
    (lo := (92822539 / 250000000)) (hi := (371290157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 883) = 1/(883 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-371290157 / 1000000000) (-92822539 / 250000000) (Real.log (883 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48334201 / 100000000) ≤ -Real.log (2560 / 4151) ∧
    -Real.log (2560 / 4151) ≤ (483342011 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 6711)) (n := 12)
    (lo := (48334201 / 100000000)) (hi := (483342011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4151 / 2560) = 1/(2560 / 4151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (48334201 / 100000000) (483342011 / 1000000000) (Real.log (4151 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4151 / 2560) = -Real.log (2560 / 4151) := by
    rw [show ((4151 / 2560) : ℝ) = ((2560 / 4151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (38859917 / 40000000) ≤ -Real.log (969 / 2560) ∧
    -Real.log (969 / 2560) ≤ (971497927 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 2249)) (n := 12)
    (lo := (55670149 / 200000000)) (hi := (139175373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 969) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 969) = 1/(969 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-971497927 / 1000000000) (-38859917 / 40000000) (Real.log (969 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (482619031 / 1000000000) ≤ -Real.log (640 / 1037) ∧
    -Real.log (640 / 1037) ≤ (60327379 / 125000000) := by
  have h := checkLog_sound (w := (397 / 1677)) (n := 12)
    (lo := (482619031 / 1000000000)) (hi := (60327379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1037 / 640) = 1/(640 / 1037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (482619031 / 1000000000) (60327379 / 125000000) (Real.log (1037 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1037 / 640) = -Real.log (640 / 1037) := by
    rw [show ((1037 / 640) : ℝ) = ((640 / 1037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (242101683 / 250000000) ≤ -Real.log (243 / 640) ∧
    -Real.log (243 / 640) ≤ (484203367 / 500000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 243) = 1/(243 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-484203367 / 500000000) (-242101683 / 250000000) (Real.log (243 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (369557407 / 1000000000) ≤ -Real.log (500000 / 723547) ∧
    -Real.log (500000 / 723547) ≤ (11548669 / 31250000) := by
  have h := checkLog_sound (w := (223547 / 1223547)) (n := 12)
    (lo := (369557407 / 1000000000)) (hi := (11548669 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723547 / 500000) = 1/(500000 / 723547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (369557407 / 1000000000) (11548669 / 31250000) (Real.log (723547 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (723547 / 500000) = -Real.log (500000 / 723547) := by
    rw [show ((723547 / 500000) : ℝ) = ((500000 / 723547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (592567273 / 1000000000) ≤ -Real.log (276453 / 500000) ∧
    -Real.log (276453 / 500000) ≤ (296283637 / 500000000) := by
  have h := checkLog_sound (w := (223547 / 776453)) (n := 12)
    (lo := (592567273 / 1000000000)) (hi := (296283637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276453) = 1/(276453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-296283637 / 500000000) (-592567273 / 1000000000) (Real.log (276453 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (370168791 / 1000000000) ≤ -Real.log (1000000 / 1447979) ∧
    -Real.log (1000000 / 1447979) ≤ (46271099 / 125000000) := by
  have h := checkLog_sound (w := (447979 / 2447979)) (n := 12)
    (lo := (370168791 / 1000000000)) (hi := (46271099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447979 / 1000000) = 1/(1000000 / 1447979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (370168791 / 1000000000) (46271099 / 125000000) (Real.log (1447979 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1447979 / 1000000) = -Real.log (1000000 / 1447979) := by
    rw [show ((1447979 / 1000000) : ℝ) = ((1000000 / 1447979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (594169189 / 1000000000) ≤ -Real.log (552021 / 1000000) ∧
    -Real.log (552021 / 1000000) ≤ (59416919 / 100000000) := by
  have h := checkLog_sound (w := (447979 / 1552021)) (n := 12)
    (lo := (594169189 / 1000000000)) (hi := (59416919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 552021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 552021) = 1/(552021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59416919 / 100000000) (-594169189 / 1000000000) (Real.log (552021 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (28864361 / 100000000) ≤ -Real.log (125000 / 166827) ∧
    -Real.log (125000 / 166827) ≤ (288643611 / 1000000000) := by
  have h := checkLog_sound (w := (41827 / 291827)) (n := 12)
    (lo := (28864361 / 100000000)) (hi := (288643611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166827 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166827 / 125000) = 1/(125000 / 166827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (28864361 / 100000000) (288643611 / 1000000000) (Real.log (166827 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (166827 / 125000) = -Real.log (125000 / 166827) := by
    rw [show ((166827 / 125000) : ℝ) = ((125000 / 166827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (407390961 / 1000000000) ≤ -Real.log (83173 / 125000) ∧
    -Real.log (83173 / 125000) ≤ (203695481 / 500000000) := by
  have h := checkLog_sound (w := (41827 / 208173)) (n := 12)
    (lo := (407390961 / 1000000000)) (hi := (203695481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 83173) = 1/(83173 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-203695481 / 500000000) (-407390961 / 1000000000) (Real.log (83173 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (144598961 / 500000000) ≤ -Real.log (250000 / 333839) ∧
    -Real.log (250000 / 333839) ≤ (289197923 / 1000000000) := by
  have h := checkLog_sound (w := (83839 / 583839)) (n := 12)
    (lo := (144598961 / 500000000)) (hi := (289197923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333839 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333839 / 250000) = 1/(250000 / 333839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144598961 / 500000000) (289197923 / 1000000000) (Real.log (333839 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (333839 / 250000) = -Real.log (250000 / 333839) := by
    rw [show ((333839 / 250000) : ℝ) = ((250000 / 333839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10212593 / 25000000) ≤ -Real.log (166161 / 250000) ∧
    -Real.log (166161 / 250000) ≤ (408503721 / 1000000000) := by
  have h := checkLog_sound (w := (83839 / 416161)) (n := 12)
    (lo := (10212593 / 25000000)) (hi := (408503721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 166161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 166161) = 1/(166161 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-408503721 / 1000000000) (-10212593 / 25000000) (Real.log (166161 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (24053117 / 25000000) ≤ -Real.log (500000000000 / 1308625697677) ∧
    -Real.log (500000000000 / 1308625697677) ≤ (481062341 / 500000000) := by
  have h := checkLog_sound (w := (308625697677 / 2308625697677)) (n := 12)
    (lo := (107591 / 400000)) (hi := (268977501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308625697677 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1308625697677 / 1000000000000) = 1/(500000000000 / 1308625697677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24053117 / 25000000) (481062341 / 500000000) (Real.log (1308625697677 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1308625697677 / 500000000000) = -Real.log (500000000000 / 1308625697677) := by
    rw [show ((1308625697677 / 500000000000) : ℝ) = ((500000000000 / 1308625697677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (48216899 / 50000000) ≤ -Real.log (15625000000 / 40985165193) ∧
    -Real.log (15625000000 / 40985165193) ≤ (482168991 / 500000000) := by
  have h := checkLog_sound (w := (9735165193 / 72235165193)) (n := 12)
    (lo := (677977 / 2500000)) (hi := (271190801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40985165193 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40985165193 / 31250000000) = 1/(15625000000 / 40985165193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (48216899 / 50000000) (482168991 / 500000000) (Real.log (40985165193 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40985165193 / 15625000000) = -Real.log (15625000000 / 40985165193) := by
    rw [show ((40985165193 / 15625000000) : ℝ) = ((15625000000 / 40985165193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (69603457 / 100000000) ≤ -Real.log (500000000000 / 1002891563367) ∧
    -Real.log (500000000000 / 1002891563367) ≤ (174008643 / 250000000) := by
  have h := checkLog_sound (w := (2891563367 / 2002891563367)) (n := 12)
    (lo := (288739 / 100000000)) (hi := (2887391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002891563367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002891563367 / 1000000000000) = 1/(500000000000 / 1002891563367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (69603457 / 100000000) (174008643 / 250000000) (Real.log (1002891563367 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1002891563367 / 500000000000) = -Real.log (500000000000 / 1002891563367) := by
    rw [show ((1002891563367 / 500000000000) : ℝ) = ((500000000000 / 1002891563367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (348850821 / 500000000) ≤ -Real.log (100000000000 / 200912969951) ∧
    -Real.log (100000000000 / 200912969951) ≤ (174425411 / 250000000) := by
  have h := checkLog_sound (w := (912969951 / 400912969951)) (n := 12)
    (lo := (2277231 / 500000000)) (hi := (4554463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200912969951 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200912969951 / 200000000000) = 1/(100000000000 / 200912969951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (348850821 / 500000000) (174425411 / 250000000) (Real.log (200912969951 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (200912969951 / 100000000000) = -Real.log (100000000000 / 200912969951) := by
    rw [show ((200912969951 / 100000000000) : ℝ) = ((100000000000 / 200912969951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0189

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0190Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0190
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

theorem reflection_log_1_neg : (67536601 / 250000000) ≤ -Real.log (1280 / 1677) ∧
    -Real.log (1280 / 1677) ≤ (54029281 / 200000000) := by
  have h := checkLog_sound (w := (397 / 2957)) (n := 12)
    (lo := (67536601 / 250000000)) (hi := (54029281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1280) = 1/(1280 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67536601 / 250000000) (54029281 / 200000000) (Real.log (1677 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1677 / 1280) = -Real.log (1280 / 1677) := by
    rw [show ((1677 / 1280) : ℝ) = ((1280 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92822539 / 250000000) ≤ -Real.log (883 / 1280) ∧
    -Real.log (883 / 1280) ≤ (371290157 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2163)) (n := 12)
    (lo := (92822539 / 250000000)) (hi := (371290157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 883) = 1/(883 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-371290157 / 1000000000) (-92822539 / 250000000) (Real.log (883 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (269699077 / 1000000000) ≤ -Real.log (1024 / 1341) ∧
    -Real.log (1024 / 1341) ≤ (134849539 / 500000000) := by
  have h := checkLog_sound (w := (317 / 2365)) (n := 12)
    (lo := (269699077 / 1000000000)) (hi := (134849539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341 / 1024) = 1/(1024 / 1341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (269699077 / 1000000000) (134849539 / 500000000) (Real.log (1341 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1341 / 1024) = -Real.log (1024 / 1341) := by
    rw [show ((1341 / 1024) : ℝ) = ((1024 / 1341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (370441139 / 1000000000) ≤ -Real.log (707 / 1024) ∧
    -Real.log (707 / 1024) ≤ (18522057 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1731)) (n := 12)
    (lo := (370441139 / 1000000000)) (hi := (18522057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 707) = 1/(707 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18522057 / 50000000) (-370441139 / 1000000000) (Real.log (707 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (482619031 / 1000000000) ≤ -Real.log (640 / 1037) ∧
    -Real.log (640 / 1037) ≤ (60327379 / 125000000) := by
  have h := checkLog_sound (w := (397 / 1677)) (n := 12)
    (lo := (482619031 / 1000000000)) (hi := (60327379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1037 / 640) = 1/(640 / 1037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (482619031 / 1000000000) (60327379 / 125000000) (Real.log (1037 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1037 / 640) = -Real.log (640 / 1037) := by
    rw [show ((1037 / 640) : ℝ) = ((640 / 1037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (242101683 / 250000000) ≤ -Real.log (243 / 640) ∧
    -Real.log (243 / 640) ≤ (484203367 / 500000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 243) = 1/(243 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-484203367 / 500000000) (-242101683 / 250000000) (Real.log (243 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48189553 / 100000000) ≤ -Real.log (512 / 829) ∧
    -Real.log (512 / 829) ≤ (481895531 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1341)) (n := 12)
    (lo := (48189553 / 100000000)) (hi := (481895531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829 / 512) = 1/(512 / 829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48189553 / 100000000) (481895531 / 1000000000) (Real.log (829 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (829 / 512) = -Real.log (512 / 829) := by
    rw [show ((829 / 512) : ℝ) = ((512 / 829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (193065013 / 200000000) ≤ -Real.log (195 / 512) ∧
    -Real.log (195 / 512) ≤ (965325067 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 451)) (n := 12)
    (lo := (54435577 / 200000000)) (hi := (136088943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 195) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 195) = 1/(195 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-965325067 / 1000000000) (-193065013 / 200000000) (Real.log (195 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (368946341 / 1000000000) ≤ -Real.log (100000 / 144621) ∧
    -Real.log (100000 / 144621) ≤ (184473171 / 500000000) := by
  have h := checkLog_sound (w := (44621 / 244621)) (n := 12)
    (lo := (368946341 / 1000000000)) (hi := (184473171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144621 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144621 / 100000) = 1/(100000 / 144621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (368946341 / 1000000000) (184473171 / 500000000) (Real.log (144621 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (144621 / 100000) = -Real.log (100000 / 144621) := by
    rw [show ((144621 / 100000) : ℝ) = ((100000 / 144621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23638789 / 40000000) ≤ -Real.log (55379 / 100000) ∧
    -Real.log (55379 / 100000) ≤ (295484863 / 500000000) := by
  have h := checkLog_sound (w := (44621 / 155379)) (n := 12)
    (lo := (23638789 / 40000000)) (hi := (295484863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 55379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 55379) = 1/(55379 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-295484863 / 500000000) (-23638789 / 40000000) (Real.log (55379 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184779049 / 500000000) ≤ -Real.log (200000 / 289419) ∧
    -Real.log (200000 / 289419) ≤ (369558099 / 1000000000) := by
  have h := checkLog_sound (w := (89419 / 489419)) (n := 12)
    (lo := (184779049 / 500000000)) (hi := (369558099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289419 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289419 / 200000) = 1/(200000 / 289419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184779049 / 500000000) (369558099 / 1000000000) (Real.log (289419 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (289419 / 200000) = -Real.log (200000 / 289419) := by
    rw [show ((289419 / 200000) : ℝ) = ((200000 / 289419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (296284541 / 500000000) ≤ -Real.log (110581 / 200000) ∧
    -Real.log (110581 / 200000) ≤ (592569083 / 1000000000) := by
  have h := checkLog_sound (w := (89419 / 310581)) (n := 12)
    (lo := (296284541 / 500000000)) (hi := (592569083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110581) = 1/(110581 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-592569083 / 1000000000) (-296284541 / 500000000) (Real.log (110581 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288090489 / 1000000000) ≤ -Real.log (500000 / 666939) ∧
    -Real.log (500000 / 666939) ≤ (28809049 / 100000000) := by
  have h := checkLog_sound (w := (166939 / 1166939)) (n := 12)
    (lo := (288090489 / 1000000000)) (hi := (28809049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666939 / 500000) = 1/(500000 / 666939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288090489 / 1000000000) (28809049 / 100000000) (Real.log (666939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (666939 / 500000) = -Real.log (500000 / 666939) := by
    rw [show ((666939 / 500000) : ℝ) = ((500000 / 666939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (203141221 / 500000000) ≤ -Real.log (333061 / 500000) ∧
    -Real.log (333061 / 500000) ≤ (406282443 / 1000000000) := by
  have h := checkLog_sound (w := (166939 / 833061)) (n := 12)
    (lo := (203141221 / 500000000)) (hi := (406282443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333061) = 1/(333061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-406282443 / 1000000000) (-203141221 / 500000000) (Real.log (333061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (288644359 / 1000000000) ≤ -Real.log (1000000 / 1334617) ∧
    -Real.log (1000000 / 1334617) ≤ (7216109 / 25000000) := by
  have h := checkLog_sound (w := (334617 / 2334617)) (n := 12)
    (lo := (288644359 / 1000000000)) (hi := (7216109 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334617 / 1000000) = 1/(1000000 / 1334617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (288644359 / 1000000000) (7216109 / 25000000) (Real.log (1334617 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1334617 / 1000000) = -Real.log (1000000 / 1334617) := by
    rw [show ((1334617 / 1000000) : ℝ) = ((1000000 / 1334617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25462029 / 62500000) ≤ -Real.log (665383 / 1000000) ∧
    -Real.log (665383 / 1000000) ≤ (81478493 / 200000000) := by
  have h := checkLog_sound (w := (334617 / 1665383)) (n := 12)
    (lo := (25462029 / 62500000)) (hi := (81478493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665383) = 1/(665383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-81478493 / 200000000) (-25462029 / 62500000) (Real.log (665383 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (479958033 / 500000000) ≤ -Real.log (500000000000 / 1305738637389) ∧
    -Real.log (500000000000 / 1305738637389) ≤ (239979017 / 250000000) := by
  have h := checkLog_sound (w := (305738637389 / 2305738637389)) (n := 12)
    (lo := (133384443 / 500000000)) (hi := (266768887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305738637389 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1305738637389 / 1000000000000) = 1/(500000000000 / 1305738637389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (479958033 / 500000000) (239979017 / 250000000) (Real.log (1305738637389 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1305738637389 / 500000000000) = -Real.log (500000000000 / 1305738637389) := by
    rw [show ((1305738637389 / 500000000000) : ℝ) = ((500000000000 / 1305738637389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (48106359 / 50000000) ≤ -Real.log (500000000000 / 1308628968811) ∧
    -Real.log (500000000000 / 1308628968811) ≤ (481063591 / 500000000) := by
  have h := checkLog_sound (w := (308628968811 / 2308628968811)) (n := 12)
    (lo := (13449 / 50000)) (hi := (268980001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308628968811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1308628968811 / 1000000000000) = 1/(500000000000 / 1308628968811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (48106359 / 50000000) (481063591 / 500000000) (Real.log (1308628968811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1308628968811 / 500000000000) = -Real.log (500000000000 / 1308628968811) := by
    rw [show ((1308628968811 / 500000000000) : ℝ) = ((500000000000 / 1308628968811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (69437293 / 100000000) ≤ -Real.log (125000000000 / 250306625513) ∧
    -Real.log (125000000000 / 250306625513) ≤ (173593233 / 250000000) := by
  have h := checkLog_sound (w := (306625513 / 500306625513)) (n := 12)
    (lo := (4903 / 4000000)) (hi := (1225751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250306625513 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250306625513 / 250000000000) = 1/(125000000000 / 250306625513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (69437293 / 100000000) (173593233 / 250000000) (Real.log (250306625513 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (250306625513 / 125000000000) = -Real.log (125000000000 / 250306625513) := by
    rw [show ((250306625513 / 125000000000) : ℝ) = ((125000000000 / 250306625513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (696036823 / 1000000000) ≤ -Real.log (100000000000 / 200578764411) ∧
    -Real.log (100000000000 / 200578764411) ≤ (27841473 / 40000000) := by
  have h := checkLog_sound (w := (578764411 / 400578764411)) (n := 12)
    (lo := (2889643 / 1000000000)) (hi := (722411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200578764411 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200578764411 / 200000000000) = 1/(100000000000 / 200578764411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (696036823 / 1000000000) (27841473 / 40000000) (Real.log (200578764411 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (200578764411 / 100000000000) = -Real.log (100000000000 / 200578764411) := by
    rw [show ((200578764411 / 100000000000) : ℝ) = ((100000000000 / 200578764411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0190

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0191Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0191
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

theorem reflection_log_1_neg : (269699077 / 1000000000) ≤ -Real.log (1024 / 1341) ∧
    -Real.log (1024 / 1341) ≤ (134849539 / 500000000) := by
  have h := checkLog_sound (w := (317 / 2365)) (n := 12)
    (lo := (269699077 / 1000000000)) (hi := (134849539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341 / 1024) = 1/(1024 / 1341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (269699077 / 1000000000) (134849539 / 500000000) (Real.log (1341 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1341 / 1024) = -Real.log (1024 / 1341) := by
    rw [show ((1341 / 1024) : ℝ) = ((1024 / 1341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (370441139 / 1000000000) ≤ -Real.log (707 / 1024) ∧
    -Real.log (707 / 1024) ≤ (18522057 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1731)) (n := 12)
    (lo := (370441139 / 1000000000)) (hi := (18522057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 707) = 1/(707 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18522057 / 50000000) (-370441139 / 1000000000) (Real.log (707 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5385031 / 20000000) ≤ -Real.log (2560 / 3351) ∧
    -Real.log (2560 / 3351) ≤ (269251551 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5911)) (n := 12)
    (lo := (5385031 / 20000000)) (hi := (269251551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3351 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3351 / 2560) = 1/(2560 / 3351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5385031 / 20000000) (269251551 / 1000000000) (Real.log (3351 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3351 / 2560) = -Real.log (2560 / 3351) := by
    rw [show ((3351 / 2560) : ℝ) = ((2560 / 3351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (369592843 / 1000000000) ≤ -Real.log (1769 / 2560) ∧
    -Real.log (1769 / 2560) ≤ (92398211 / 250000000) := by
  have h := checkLog_sound (w := (791 / 4329)) (n := 12)
    (lo := (369592843 / 1000000000)) (hi := (92398211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1769) = 1/(1769 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-92398211 / 250000000) (-369592843 / 1000000000) (Real.log (1769 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48189553 / 100000000) ≤ -Real.log (512 / 829) ∧
    -Real.log (512 / 829) ≤ (481895531 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1341)) (n := 12)
    (lo := (48189553 / 100000000)) (hi := (481895531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829 / 512) = 1/(512 / 829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (48189553 / 100000000) (481895531 / 1000000000) (Real.log (829 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (829 / 512) = -Real.log (512 / 829) := by
    rw [show ((829 / 512) : ℝ) = ((512 / 829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (193065013 / 200000000) ≤ -Real.log (195 / 512) ∧
    -Real.log (195 / 512) ≤ (965325067 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 451)) (n := 12)
    (lo := (54435577 / 200000000)) (hi := (136088943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 195) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 195) = 1/(195 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-965325067 / 1000000000) (-193065013 / 200000000) (Real.log (195 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30073219 / 62500000) ≤ -Real.log (1280 / 2071) ∧
    -Real.log (1280 / 2071) ≤ (96234301 / 200000000) := by
  have h := checkLog_sound (w := (791 / 3351)) (n := 12)
    (lo := (30073219 / 62500000)) (hi := (96234301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2071 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2071 / 1280) = 1/(1280 / 2071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30073219 / 62500000) (96234301 / 200000000) (Real.log (2071 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2071 / 1280) = -Real.log (1280 / 2071) := by
    rw [show ((2071 / 1280) : ℝ) = ((1280 / 2071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (481126433 / 500000000) ≤ -Real.log (489 / 1280) ∧
    -Real.log (489 / 1280) ≤ (240563217 / 250000000) := by
  have h := checkLog_sound (w := (151 / 1129)) (n := 12)
    (lo := (134552843 / 500000000)) (hi := (269105687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 489) = 1/(489 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240563217 / 250000000) (-481126433 / 500000000) (Real.log (489 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (368335593 / 1000000000) ≤ -Real.log (1000000 / 1445327) ∧
    -Real.log (1000000 / 1445327) ≤ (184167797 / 500000000) := by
  have h := checkLog_sound (w := (445327 / 2445327)) (n := 12)
    (lo := (368335593 / 1000000000)) (hi := (184167797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445327 / 1000000) = 1/(1000000 / 1445327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (368335593 / 1000000000) (184167797 / 500000000) (Real.log (1445327 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1445327 / 1000000) = -Real.log (1000000 / 1445327) := by
    rw [show ((1445327 / 1000000) : ℝ) = ((1000000 / 1445327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36836033 / 62500000) ≤ -Real.log (554673 / 1000000) ∧
    -Real.log (554673 / 1000000) ≤ (589376529 / 1000000000) := by
  have h := checkLog_sound (w := (445327 / 1554673)) (n := 12)
    (lo := (36836033 / 62500000)) (hi := (589376529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 554673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 554673) = 1/(554673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-589376529 / 1000000000) (-36836033 / 62500000) (Real.log (554673 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92236931 / 250000000) ≤ -Real.log (250000 / 361553) ∧
    -Real.log (250000 / 361553) ≤ (14757909 / 40000000) := by
  have h := checkLog_sound (w := (111553 / 611553)) (n := 12)
    (lo := (92236931 / 250000000)) (hi := (14757909 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361553 / 250000) = 1/(250000 / 361553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92236931 / 250000000) (14757909 / 40000000) (Real.log (361553 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (361553 / 250000) = -Real.log (250000 / 361553) := by
    rw [show ((361553 / 250000) : ℝ) = ((250000 / 361553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73871667 / 125000000) ≤ -Real.log (138447 / 250000) ∧
    -Real.log (138447 / 250000) ≤ (590973337 / 1000000000) := by
  have h := checkLog_sound (w := (111553 / 388447)) (n := 12)
    (lo := (73871667 / 125000000)) (hi := (590973337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 138447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 138447) = 1/(138447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-590973337 / 1000000000) (-73871667 / 125000000) (Real.log (138447 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (71884453 / 250000000) ≤ -Real.log (1000000 / 1333141) ∧
    -Real.log (1000000 / 1333141) ≤ (287537813 / 1000000000) := by
  have h := checkLog_sound (w := (333141 / 2333141)) (n := 12)
    (lo := (71884453 / 250000000)) (hi := (287537813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333141 / 1000000) = 1/(1000000 / 1333141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (71884453 / 250000000) (287537813 / 1000000000) (Real.log (1333141 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1333141 / 1000000) = -Real.log (1000000 / 1333141) := by
    rw [show ((1333141 / 1000000) : ℝ) = ((1000000 / 1333141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (405176649 / 1000000000) ≤ -Real.log (666859 / 1000000) ∧
    -Real.log (666859 / 1000000) ≤ (8103533 / 20000000) := by
  have h := checkLog_sound (w := (333141 / 1666859)) (n := 12)
    (lo := (405176649 / 1000000000)) (hi := (8103533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666859) = 1/(666859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8103533 / 20000000) (-405176649 / 1000000000) (Real.log (666859 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (144045619 / 500000000) ≤ -Real.log (1000000 / 1333879) ∧
    -Real.log (1000000 / 1333879) ≤ (288091239 / 1000000000) := by
  have h := checkLog_sound (w := (333879 / 2333879)) (n := 12)
    (lo := (144045619 / 500000000)) (hi := (288091239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333879 / 1000000) = 1/(1000000 / 1333879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144045619 / 500000000) (288091239 / 1000000000) (Real.log (1333879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1333879 / 1000000) = -Real.log (1000000 / 1333879) := by
    rw [show ((1333879 / 1000000) : ℝ) = ((1000000 / 1333879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (406283943 / 1000000000) ≤ -Real.log (666121 / 1000000) ∧
    -Real.log (666121 / 1000000) ≤ (50785493 / 125000000) := by
  have h := checkLog_sound (w := (333879 / 1666121)) (n := 12)
    (lo := (406283943 / 1000000000)) (hi := (50785493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666121) = 1/(666121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-50785493 / 125000000) (-406283943 / 1000000000) (Real.log (666121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (957712121 / 1000000000) ≤ -Real.log (500000000000 / 1302864029797) ∧
    -Real.log (500000000000 / 1302864029797) ≤ (957712123 / 1000000000) := by
  have h := checkLog_sound (w := (302864029797 / 2302864029797)) (n := 12)
    (lo := (264564941 / 1000000000)) (hi := (132282471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302864029797 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1302864029797 / 1000000000000) = 1/(500000000000 / 1302864029797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (957712121 / 1000000000) (957712123 / 1000000000) (Real.log (1302864029797 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1302864029797 / 500000000000) = -Real.log (500000000000 / 1302864029797) := by
    rw [show ((1302864029797 / 500000000000) : ℝ) = ((500000000000 / 1302864029797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (47996053 / 50000000) ≤ -Real.log (250000000000 / 652872579399) ∧
    -Real.log (250000000000 / 652872579399) ≤ (479960531 / 500000000) := by
  have h := checkLog_sound (w := (152872579399 / 1152872579399)) (n := 12)
    (lo := (6669347 / 25000000)) (hi := (266773881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652872579399 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(652872579399 / 500000000000) = 1/(250000000000 / 652872579399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (47996053 / 50000000) (479960531 / 500000000) (Real.log (652872579399 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (652872579399 / 250000000000) = -Real.log (250000000000 / 652872579399) := by
    rw [show ((652872579399 / 250000000000) : ℝ) = ((250000000000 / 652872579399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (692714461 / 1000000000) ≤ -Real.log (125000000000 / 249891843703) ∧
    -Real.log (125000000000 / 249891843703) ≤ (346357231 / 500000000) := by
  have h := checkLog_sound (w := (124891843703 / 374891843703)) (n := 12)
    (lo := (692714461 / 1000000000)) (hi := (346357231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249891843703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249891843703 / 125000000000) = 1/(125000000000 / 249891843703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (692714461 / 1000000000) (346357231 / 500000000) (Real.log (249891843703 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (249891843703 / 125000000000) = -Real.log (125000000000 / 249891843703) := by
    rw [show ((249891843703 / 125000000000) : ℝ) = ((125000000000 / 249891843703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (694375181 / 1000000000) ≤ -Real.log (500000000000 / 1001228755737) ∧
    -Real.log (500000000000 / 1001228755737) ≤ (694375183 / 1000000000) := by
  have h := checkLog_sound (w := (1228755737 / 2001228755737)) (n := 12)
    (lo := (1228001 / 1000000000)) (hi := (614001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001228755737 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1001228755737 / 1000000000000) = 1/(500000000000 / 1001228755737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (694375181 / 1000000000) (694375183 / 1000000000) (Real.log (1001228755737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1001228755737 / 500000000000) = -Real.log (500000000000 / 1001228755737) := by
    rw [show ((1001228755737 / 500000000000) : ℝ) = ((500000000000 / 1001228755737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0191

end


