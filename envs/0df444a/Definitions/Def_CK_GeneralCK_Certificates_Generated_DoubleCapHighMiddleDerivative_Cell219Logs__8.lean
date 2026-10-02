-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell219Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell219Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:52:27.014796+00:00
-- url     : https://prove2.me/theorems/a9dbae1a-5117-4312-a68f-97dcef8e8d9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell219Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell220…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell219Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell220Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell221Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell222Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell223Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell224Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell225Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell226Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell219Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell220Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell221Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell222Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell223Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell224Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell225Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell226Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell219Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell220Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell221Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell222Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell223Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell224Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell225Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell226Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell219Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell220Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell221Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell222Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell223Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell224Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell225Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell226Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell219Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell219
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

theorem reflection_log_1_neg : (80322653 / 250000000) ≤ -Real.log (256 / 353) ∧
    -Real.log (256 / 353) ≤ (321290613 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 609)) (n := 12)
    (lo := (80322653 / 250000000)) (hi := (321290613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353 / 256) = 1/(256 / 353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80322653 / 250000000) (321290613 / 1000000000) (Real.log (353 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (353 / 256) = -Real.log (256 / 353) := by
    rw [show ((353 / 256) : ℝ) = ((256 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (238136621 / 500000000) ≤ -Real.log (159 / 256) ∧
    -Real.log (159 / 256) ≤ (476273243 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 415)) (n := 12)
    (lo := (238136621 / 500000000)) (hi := (476273243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 159) = 1/(159 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-476273243 / 1000000000) (-238136621 / 500000000) (Real.log (159 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40108199 / 125000000) ≤ -Real.log (5120 / 7057) ∧
    -Real.log (5120 / 7057) ≤ (320865593 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 12177)) (n := 12)
    (lo := (40108199 / 125000000)) (hi := (320865593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7057 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7057 / 5120) = 1/(5120 / 7057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40108199 / 125000000) (320865593 / 1000000000) (Real.log (7057 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7057 / 5120) = -Real.log (5120 / 7057) := by
    rw [show ((7057 / 5120) : ℝ) = ((5120 / 7057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47533029 / 100000000) ≤ -Real.log (3183 / 5120) ∧
    -Real.log (3183 / 5120) ≤ (475330291 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 8303)) (n := 12)
    (lo := (47533029 / 100000000)) (hi := (475330291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3183) = 1/(3183 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-475330291 / 1000000000) (-47533029 / 100000000) (Real.log (3183 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (238394659 / 1000000000) ≤ -Real.log (100000 / 126921) ∧
    -Real.log (100000 / 126921) ≤ (11919733 / 50000000) := by
  have h := checkLog_sound (w := (26921 / 226921)) (n := 12)
    (lo := (238394659 / 1000000000)) (hi := (11919733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126921 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126921 / 100000) = 1/(100000 / 126921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (238394659 / 1000000000) (11919733 / 50000000) (Real.log (126921 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (126921 / 100000) = -Real.log (100000 / 126921) := by
    rw [show ((126921 / 100000) : ℝ) = ((100000 / 126921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156814569 / 500000000) ≤ -Real.log (73079 / 100000) ∧
    -Real.log (73079 / 100000) ≤ (313629139 / 1000000000) := by
  have h := checkLog_sound (w := (26921 / 173079)) (n := 12)
    (lo := (156814569 / 500000000)) (hi := (313629139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73079) = 1/(73079 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-313629139 / 1000000000) (-156814569 / 500000000) (Real.log (73079 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (238728669 / 1000000000) ≤ -Real.log (500000 / 634817) ∧
    -Real.log (500000 / 634817) ≤ (23872867 / 100000000) := by
  have h := checkLog_sound (w := (134817 / 1134817)) (n := 12)
    (lo := (238728669 / 1000000000)) (hi := (23872867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634817 / 500000) = 1/(500000 / 634817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (238728669 / 1000000000) (23872867 / 100000000) (Real.log (634817 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (634817 / 500000) = -Real.log (500000 / 634817) := by
    rw [show ((634817 / 500000) : ℝ) = ((500000 / 634817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (628419 / 2000000) ≤ -Real.log (365183 / 500000) ∧
    -Real.log (365183 / 500000) ≤ (314209501 / 1000000000) := by
  have h := checkLog_sound (w := (134817 / 865183)) (n := 12)
    (lo := (628419 / 2000000)) (hi := (314209501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365183) = 1/(365183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-314209501 / 1000000000) (-628419 / 2000000) (Real.log (365183 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88763373 / 500000000) ≤ -Real.log (50000 / 59713) ∧
    -Real.log (50000 / 59713) ≤ (177526747 / 1000000000) := by
  have h := checkLog_sound (w := (9713 / 109713)) (n := 12)
    (lo := (88763373 / 500000000)) (hi := (177526747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59713 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59713 / 50000) = 1/(50000 / 59713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88763373 / 500000000) (177526747 / 1000000000) (Real.log (59713 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (59713 / 50000) = -Real.log (50000 / 59713) := by
    rw [show ((59713 / 50000) : ℝ) = ((50000 / 59713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (215994169 / 1000000000) ≤ -Real.log (40287 / 50000) ∧
    -Real.log (40287 / 50000) ≤ (21599417 / 100000000) := by
  have h := checkLog_sound (w := (9713 / 90287)) (n := 12)
    (lo := (215994169 / 1000000000)) (hi := (21599417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40287) = 1/(40287 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21599417 / 100000000) (-215994169 / 1000000000) (Real.log (40287 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (22224123 / 125000000) ≤ -Real.log (500000 / 597289) ∧
    -Real.log (500000 / 597289) ≤ (35558597 / 200000000) := by
  have h := checkLog_sound (w := (97289 / 1097289)) (n := 12)
    (lo := (22224123 / 125000000)) (hi := (35558597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597289 / 500000) = 1/(500000 / 597289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (22224123 / 125000000) (35558597 / 200000000) (Real.log (597289 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (597289 / 500000) = -Real.log (500000 / 597289) := by
    rw [show ((597289 / 500000) : ℝ) = ((500000 / 597289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43277783 / 200000000) ≤ -Real.log (402711 / 500000) ∧
    -Real.log (402711 / 500000) ≤ (54097229 / 250000000) := by
  have h := checkLog_sound (w := (97289 / 902711)) (n := 12)
    (lo := (43277783 / 200000000)) (hi := (54097229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402711) = 1/(402711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-54097229 / 250000000) (-43277783 / 200000000) (Real.log (402711 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (796195883 / 1000000000) ≤ -Real.log (500000000000 / 1108545397423) ∧
    -Real.log (500000000000 / 1108545397423) ≤ (159239177 / 200000000) := by
  have h := checkLog_sound (w := (108545397423 / 2108545397423)) (n := 12)
    (lo := (103048703 / 1000000000)) (hi := (201267 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108545397423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1108545397423 / 1000000000000) = 1/(500000000000 / 1108545397423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (796195883 / 1000000000) (159239177 / 200000000) (Real.log (1108545397423 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1108545397423 / 500000000000) = -Real.log (500000000000 / 1108545397423) := by
    rw [show ((1108545397423 / 500000000000) : ℝ) = ((500000000000 / 1108545397423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (398781927 / 500000000) ≤ -Real.log (250000000000 / 555031446541) ∧
    -Real.log (250000000000 / 555031446541) ≤ (49847741 / 62500000) := by
  have h := checkLog_sound (w := (55031446541 / 1055031446541)) (n := 12)
    (lo := (52208337 / 500000000)) (hi := (4176667 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555031446541 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555031446541 / 500000000000) = 1/(250000000000 / 555031446541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (398781927 / 500000000) (49847741 / 62500000) (Real.log (555031446541 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (555031446541 / 250000000000) = -Real.log (250000000000 / 555031446541) := by
    rw [show ((555031446541 / 250000000000) : ℝ) = ((250000000000 / 555031446541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (552023797 / 1000000000) ≤ -Real.log (50000000000 / 86838216177) ∧
    -Real.log (50000000000 / 86838216177) ≤ (276011899 / 500000000) := by
  have h := checkLog_sound (w := (36838216177 / 136838216177)) (n := 12)
    (lo := (552023797 / 1000000000)) (hi := (276011899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86838216177 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86838216177 / 50000000000) = 1/(50000000000 / 86838216177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (552023797 / 1000000000) (276011899 / 500000000) (Real.log (86838216177 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (86838216177 / 50000000000) = -Real.log (50000000000 / 86838216177) := by
    rw [show ((86838216177 / 50000000000) : ℝ) = ((50000000000 / 86838216177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55293817 / 100000000) ≤ -Real.log (6250000000 / 10864706873) ∧
    -Real.log (6250000000 / 10864706873) ≤ (552938171 / 1000000000) := by
  have h := checkLog_sound (w := (4614706873 / 17114706873)) (n := 12)
    (lo := (55293817 / 100000000)) (hi := (552938171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10864706873 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10864706873 / 6250000000) = 1/(6250000000 / 10864706873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (55293817 / 100000000) (552938171 / 1000000000) (Real.log (10864706873 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (10864706873 / 6250000000) = -Real.log (6250000000 / 10864706873) := by
    rw [show ((10864706873 / 6250000000) : ℝ) = ((6250000000 / 10864706873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (78704183 / 200000000) ≤ -Real.log (500000000000 / 741095142353) ∧
    -Real.log (500000000000 / 741095142353) ≤ (98380229 / 250000000) := by
  have h := checkLog_sound (w := (241095142353 / 1241095142353)) (n := 12)
    (lo := (78704183 / 200000000)) (hi := (98380229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741095142353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741095142353 / 500000000000) = 1/(500000000000 / 741095142353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78704183 / 200000000) (98380229 / 250000000) (Real.log (741095142353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (741095142353 / 500000000000) = -Real.log (500000000000 / 741095142353) := by
    rw [show ((741095142353 / 500000000000) : ℝ) = ((500000000000 / 741095142353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3941819 / 10000000) ≤ -Real.log (250000000000 / 370792578301) ∧
    -Real.log (250000000000 / 370792578301) ≤ (394181901 / 1000000000) := by
  have h := checkLog_sound (w := (120792578301 / 620792578301)) (n := 12)
    (lo := (3941819 / 10000000)) (hi := (394181901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370792578301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370792578301 / 250000000000) = 1/(250000000000 / 370792578301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3941819 / 10000000) (394181901 / 1000000000) (Real.log (370792578301 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (370792578301 / 250000000000) = -Real.log (250000000000 / 370792578301) := by
    rw [show ((370792578301 / 250000000000) : ℝ) = ((250000000000 / 370792578301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3859593 / 100000000) ≤ -Real.log (240534850479 / 250000000000) ∧
    -Real.log (240534850479 / 250000000000) ≤ (38595931 / 1000000000) := by
  have h := checkLog_sound (w := (9465149521 / 490534850479)) (n := 12)
    (lo := (3859593 / 100000000)) (hi := (38595931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240534850479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240534850479) = 1/(240534850479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38595931 / 1000000000) (-3859593 / 100000000) (Real.log (240534850479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19233711 / 500000000) ≤ -Real.log (2405657631 / 2500000000) ∧
    -Real.log (2405657631 / 2500000000) ≤ (38467423 / 1000000000) := by
  have h := checkLog_sound (w := (94342369 / 4905657631)) (n := 12)
    (lo := (19233711 / 500000000)) (hi := (38467423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2405657631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2405657631) = 1/(2405657631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-38467423 / 1000000000) (-19233711 / 500000000) (Real.log (2405657631 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell219

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell220Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell220
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

theorem reflection_log_1_neg : (321715451 / 1000000000) ≤ -Real.log (5120 / 7063) ∧
    -Real.log (5120 / 7063) ≤ (80428863 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 12183)) (n := 12)
    (lo := (321715451 / 1000000000)) (hi := (80428863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7063 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7063 / 5120) = 1/(5120 / 7063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (321715451 / 1000000000) (80428863 / 250000000) (Real.log (7063 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7063 / 5120) = -Real.log (5120 / 7063) := by
    rw [show ((7063 / 5120) : ℝ) = ((5120 / 7063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (477217083 / 1000000000) ≤ -Real.log (3177 / 5120) ∧
    -Real.log (3177 / 5120) ≤ (119304271 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 8297)) (n := 12)
    (lo := (477217083 / 1000000000)) (hi := (119304271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3177) = 1/(3177 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-119304271 / 250000000) (-477217083 / 1000000000) (Real.log (3177 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80322653 / 250000000) ≤ -Real.log (256 / 353) ∧
    -Real.log (256 / 353) ≤ (321290613 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 609)) (n := 12)
    (lo := (80322653 / 250000000)) (hi := (321290613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353 / 256) = 1/(256 / 353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80322653 / 250000000) (321290613 / 1000000000) (Real.log (353 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (353 / 256) = -Real.log (256 / 353) := by
    rw [show ((353 / 256) : ℝ) = ((256 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (238136621 / 500000000) ≤ -Real.log (159 / 256) ∧
    -Real.log (159 / 256) ≤ (476273243 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 415)) (n := 12)
    (lo := (238136621 / 500000000)) (hi := (476273243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 159) = 1/(159 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-476273243 / 1000000000) (-238136621 / 500000000) (Real.log (159 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119363941 / 500000000) ≤ -Real.log (1000000 / 1269633) ∧
    -Real.log (1000000 / 1269633) ≤ (238727883 / 1000000000) := by
  have h := checkLog_sound (w := (269633 / 2269633)) (n := 12)
    (lo := (119363941 / 500000000)) (hi := (238727883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269633 / 1000000) = 1/(1000000 / 1269633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119363941 / 500000000) (238727883 / 1000000000) (Real.log (1269633 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1269633 / 1000000) = -Real.log (1000000 / 1269633) := by
    rw [show ((1269633 / 1000000) : ℝ) = ((1000000 / 1269633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (314208131 / 1000000000) ≤ -Real.log (730367 / 1000000) ∧
    -Real.log (730367 / 1000000) ≤ (78552033 / 250000000) := by
  have h := checkLog_sound (w := (269633 / 1730367)) (n := 12)
    (lo := (314208131 / 1000000000)) (hi := (78552033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730367) = 1/(730367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78552033 / 250000000) (-314208131 / 1000000000) (Real.log (730367 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239060993 / 1000000000) ≤ -Real.log (125000 / 158757) ∧
    -Real.log (125000 / 158757) ≤ (119530497 / 500000000) := by
  have h := checkLog_sound (w := (33757 / 283757)) (n := 12)
    (lo := (239060993 / 1000000000)) (hi := (119530497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158757 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158757 / 125000) = 1/(125000 / 158757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239060993 / 1000000000) (119530497 / 500000000) (Real.log (158757 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158757 / 125000) = -Real.log (125000 / 158757) := by
    rw [show ((158757 / 125000) : ℝ) = ((125000 / 158757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (15739373 / 50000000) ≤ -Real.log (91243 / 125000) ∧
    -Real.log (91243 / 125000) ≤ (314787461 / 1000000000) := by
  have h := checkLog_sound (w := (33757 / 216243)) (n := 12)
    (lo := (15739373 / 50000000)) (hi := (314787461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91243) = 1/(91243 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-314787461 / 1000000000) (-15739373 / 50000000) (Real.log (91243 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177792147 / 1000000000) ≤ -Real.log (1000000 / 1194577) ∧
    -Real.log (1000000 / 1194577) ≤ (44448037 / 250000000) := by
  have h := checkLog_sound (w := (194577 / 2194577)) (n := 12)
    (lo := (177792147 / 1000000000)) (hi := (44448037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194577 / 1000000) = 1/(1000000 / 1194577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177792147 / 1000000000) (44448037 / 250000000) (Real.log (1194577 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1194577 / 1000000) = -Real.log (1000000 / 1194577) := by
    rw [show ((1194577 / 1000000) : ℝ) = ((1000000 / 1194577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (216387673 / 1000000000) ≤ -Real.log (805423 / 1000000) ∧
    -Real.log (805423 / 1000000) ≤ (108193837 / 500000000) := by
  have h := checkLog_sound (w := (194577 / 1805423)) (n := 12)
    (lo := (216387673 / 1000000000)) (hi := (108193837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805423) = 1/(805423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-108193837 / 500000000) (-216387673 / 1000000000) (Real.log (805423 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11128697 / 62500000) ≤ -Real.log (62500 / 74681) ∧
    -Real.log (62500 / 74681) ≤ (178059153 / 1000000000) := by
  have h := checkLog_sound (w := (12181 / 137181)) (n := 12)
    (lo := (11128697 / 62500000)) (hi := (178059153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74681 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74681 / 62500) = 1/(62500 / 74681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11128697 / 62500000) (178059153 / 1000000000) (Real.log (74681 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (74681 / 62500) = -Real.log (62500 / 74681) := by
    rw [show ((74681 / 62500) : ℝ) = ((62500 / 74681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (216783817 / 1000000000) ≤ -Real.log (50319 / 62500) ∧
    -Real.log (50319 / 62500) ≤ (108391909 / 500000000) := by
  have h := checkLog_sound (w := (12181 / 112819)) (n := 12)
    (lo := (216783817 / 1000000000)) (hi := (108391909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50319) = 1/(50319 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-108391909 / 500000000) (-216783817 / 1000000000) (Real.log (50319 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (398781927 / 500000000) ≤ -Real.log (500000000000 / 1110062893081) ∧
    -Real.log (500000000000 / 1110062893081) ≤ (49847741 / 62500000) := by
  have h := checkLog_sound (w := (110062893081 / 2110062893081)) (n := 12)
    (lo := (52208337 / 500000000)) (hi := (4176667 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110062893081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110062893081 / 1000000000000) = 1/(500000000000 / 1110062893081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (398781927 / 500000000) (49847741 / 62500000) (Real.log (1110062893081 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1110062893081 / 500000000000) = -Real.log (500000000000 / 1110062893081) := by
    rw [show ((1110062893081 / 500000000000) : ℝ) = ((500000000000 / 1110062893081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (399466267 / 500000000) ≤ -Real.log (500000000000 / 1111583254643) ∧
    -Real.log (500000000000 / 1111583254643) ≤ (99866567 / 125000000) := by
  have h := checkLog_sound (w := (111583254643 / 2111583254643)) (n := 12)
    (lo := (52892677 / 500000000)) (hi := (21157071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111583254643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1111583254643 / 1000000000000) = 1/(500000000000 / 1111583254643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (399466267 / 500000000) (99866567 / 125000000) (Real.log (1111583254643 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1111583254643 / 500000000000) = -Real.log (500000000000 / 1111583254643) := by
    rw [show ((1111583254643 / 500000000000) : ℝ) = ((500000000000 / 1111583254643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (552936013 / 1000000000) ≤ -Real.log (500000000000 / 869174675197) ∧
    -Real.log (500000000000 / 869174675197) ≤ (276468007 / 500000000) := by
  have h := checkLog_sound (w := (369174675197 / 1369174675197)) (n := 12)
    (lo := (552936013 / 1000000000)) (hi := (276468007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869174675197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869174675197 / 500000000000) = 1/(500000000000 / 869174675197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (552936013 / 1000000000) (276468007 / 500000000) (Real.log (869174675197 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (869174675197 / 500000000000) = -Real.log (500000000000 / 869174675197) := by
    rw [show ((869174675197 / 500000000000) : ℝ) = ((500000000000 / 869174675197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276924227 / 500000000) ≤ -Real.log (500000000000 / 869968107143) ∧
    -Real.log (500000000000 / 869968107143) ≤ (110769691 / 200000000) := by
  have h := checkLog_sound (w := (369968107143 / 1369968107143)) (n := 12)
    (lo := (276924227 / 500000000)) (hi := (110769691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869968107143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869968107143 / 500000000000) = 1/(500000000000 / 869968107143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (276924227 / 500000000) (110769691 / 200000000) (Real.log (869968107143 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (869968107143 / 500000000000) = -Real.log (500000000000 / 869968107143) := by
    rw [show ((869968107143 / 500000000000) : ℝ) = ((500000000000 / 869968107143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (394179821 / 1000000000) ≤ -Real.log (500000000000 / 741583615069) ∧
    -Real.log (500000000000 / 741583615069) ≤ (197089911 / 500000000) := by
  have h := checkLog_sound (w := (241583615069 / 1241583615069)) (n := 12)
    (lo := (394179821 / 1000000000)) (hi := (197089911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741583615069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741583615069 / 500000000000) = 1/(500000000000 / 741583615069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (394179821 / 1000000000) (197089911 / 500000000) (Real.log (741583615069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (741583615069 / 500000000000) = -Real.log (500000000000 / 741583615069) := by
    rw [show ((741583615069 / 500000000000) : ℝ) = ((500000000000 / 741583615069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (394842969 / 1000000000) ≤ -Real.log (500000000000 / 742075557941) ∧
    -Real.log (500000000000 / 742075557941) ≤ (39484297 / 100000000) := by
  have h := checkLog_sound (w := (242075557941 / 1242075557941)) (n := 12)
    (lo := (394842969 / 1000000000)) (hi := (39484297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742075557941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742075557941 / 500000000000) = 1/(500000000000 / 742075557941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (394842969 / 1000000000) (39484297 / 100000000) (Real.log (742075557941 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (742075557941 / 500000000000) = -Real.log (500000000000 / 742075557941) := by
    rw [show ((742075557941 / 500000000000) : ℝ) = ((500000000000 / 742075557941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7744933 / 200000000) ≤ -Real.log (3757873239 / 3906250000) ∧
    -Real.log (3757873239 / 3906250000) ≤ (19362333 / 500000000) := by
  have h := checkLog_sound (w := (148376761 / 7664123239)) (n := 12)
    (lo := (7744933 / 200000000)) (hi := (19362333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3757873239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3757873239) = 1/(3757873239 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19362333 / 500000000) (-7744933 / 200000000) (Real.log (3757873239 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1543821 / 40000000) ≤ -Real.log (962139791071 / 1000000000000) ∧
    -Real.log (962139791071 / 1000000000000) ≤ (19297763 / 500000000) := by
  have h := checkLog_sound (w := (37860208929 / 1962139791071)) (n := 12)
    (lo := (1543821 / 40000000)) (hi := (19297763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962139791071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962139791071) = 1/(962139791071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19297763 / 500000000) (-1543821 / 40000000) (Real.log (962139791071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell220

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell221Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell221
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

theorem reflection_log_1_neg : (322140109 / 1000000000) ≤ -Real.log (2560 / 3533) ∧
    -Real.log (2560 / 3533) ≤ (32214011 / 100000000) := by
  have h := checkLog_sound (w := (973 / 6093)) (n := 12)
    (lo := (322140109 / 1000000000)) (hi := (32214011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3533 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3533 / 2560) = 1/(2560 / 3533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (322140109 / 1000000000) (32214011 / 100000000) (Real.log (3533 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3533 / 2560) = -Real.log (2560 / 3533) := by
    rw [show ((3533 / 2560) : ℝ) = ((2560 / 3533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (59770227 / 125000000) ≤ -Real.log (1587 / 2560) ∧
    -Real.log (1587 / 2560) ≤ (478161817 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 4147)) (n := 12)
    (lo := (59770227 / 125000000)) (hi := (478161817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1587) = 1/(1587 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-478161817 / 1000000000) (-59770227 / 125000000) (Real.log (1587 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (321715451 / 1000000000) ≤ -Real.log (5120 / 7063) ∧
    -Real.log (5120 / 7063) ≤ (80428863 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 12183)) (n := 12)
    (lo := (321715451 / 1000000000)) (hi := (80428863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7063 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7063 / 5120) = 1/(5120 / 7063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (321715451 / 1000000000) (80428863 / 250000000) (Real.log (7063 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7063 / 5120) = -Real.log (5120 / 7063) := by
    rw [show ((7063 / 5120) : ℝ) = ((5120 / 7063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (477217083 / 1000000000) ≤ -Real.log (3177 / 5120) ∧
    -Real.log (3177 / 5120) ≤ (119304271 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 8297)) (n := 12)
    (lo := (477217083 / 1000000000)) (hi := (119304271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3177) = 1/(3177 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-119304271 / 250000000) (-477217083 / 1000000000) (Real.log (3177 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119530103 / 500000000) ≤ -Real.log (200000 / 254011) ∧
    -Real.log (200000 / 254011) ≤ (239060207 / 1000000000) := by
  have h := checkLog_sound (w := (54011 / 454011)) (n := 12)
    (lo := (119530103 / 500000000)) (hi := (239060207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254011 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254011 / 200000) = 1/(200000 / 254011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119530103 / 500000000) (239060207 / 1000000000) (Real.log (254011 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (254011 / 200000) = -Real.log (200000 / 254011) := by
    rw [show ((254011 / 200000) : ℝ) = ((200000 / 254011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31478609 / 100000000) ≤ -Real.log (145989 / 200000) ∧
    -Real.log (145989 / 200000) ≤ (314786091 / 1000000000) := by
  have h := checkLog_sound (w := (54011 / 345989)) (n := 12)
    (lo := (31478609 / 100000000)) (hi := (314786091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145989) = 1/(145989 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-314786091 / 1000000000) (-31478609 / 100000000) (Real.log (145989 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119696997 / 500000000) ≤ -Real.log (1000000 / 1270479) ∧
    -Real.log (1000000 / 1270479) ≤ (47878799 / 200000000) := by
  have h := checkLog_sound (w := (270479 / 2270479)) (n := 12)
    (lo := (119696997 / 500000000)) (hi := (47878799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270479 / 1000000) = 1/(1000000 / 1270479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119696997 / 500000000) (47878799 / 200000000) (Real.log (1270479 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1270479 / 1000000) = -Real.log (1000000 / 1270479) := by
    rw [show ((1270479 / 1000000) : ℝ) = ((1000000 / 1270479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (78841781 / 250000000) ≤ -Real.log (729521 / 1000000) ∧
    -Real.log (729521 / 1000000) ≤ (2522937 / 8000000) := by
  have h := checkLog_sound (w := (270479 / 1729521)) (n := 12)
    (lo := (78841781 / 250000000)) (hi := (2522937 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729521) = 1/(729521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2522937 / 8000000) (-78841781 / 250000000) (Real.log (729521 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35611663 / 200000000) ≤ -Real.log (200000 / 238979) ∧
    -Real.log (200000 / 238979) ≤ (44514579 / 250000000) := by
  have h := checkLog_sound (w := (38979 / 438979)) (n := 12)
    (lo := (35611663 / 200000000)) (hi := (44514579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238979 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238979 / 200000) = 1/(200000 / 238979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35611663 / 200000000) (44514579 / 250000000) (Real.log (238979 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (238979 / 200000) = -Real.log (200000 / 238979) := by
    rw [show ((238979 / 200000) : ℝ) = ((200000 / 238979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8671303 / 40000000) ≤ -Real.log (161021 / 200000) ∧
    -Real.log (161021 / 200000) ≤ (13548911 / 62500000) := by
  have h := checkLog_sound (w := (38979 / 361021)) (n := 12)
    (lo := (8671303 / 40000000)) (hi := (13548911 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161021) = 1/(161021 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13548911 / 62500000) (-8671303 / 40000000) (Real.log (161021 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (44581103 / 250000000) ≤ -Real.log (1000000 / 1195213) ∧
    -Real.log (1000000 / 1195213) ≤ (178324413 / 1000000000) := by
  have h := checkLog_sound (w := (195213 / 2195213)) (n := 12)
    (lo := (44581103 / 250000000)) (hi := (178324413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195213 / 1000000) = 1/(1000000 / 1195213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (44581103 / 250000000) (178324413 / 1000000000) (Real.log (1195213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195213 / 1000000) = -Real.log (1000000 / 1195213) := by
    rw [show ((1195213 / 1000000) : ℝ) = ((1000000 / 1195213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6786801 / 31250000) ≤ -Real.log (804787 / 1000000) ∧
    -Real.log (804787 / 1000000) ≤ (217177633 / 1000000000) := by
  have h := checkLog_sound (w := (195213 / 1804787)) (n := 12)
    (lo := (6786801 / 31250000)) (hi := (217177633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804787) = 1/(804787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217177633 / 1000000000) (-6786801 / 31250000) (Real.log (804787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (399466267 / 500000000) ≤ -Real.log (250000000000 / 555791627321) ∧
    -Real.log (250000000000 / 555791627321) ≤ (99866567 / 125000000) := by
  have h := checkLog_sound (w := (55791627321 / 1055791627321)) (n := 12)
    (lo := (52892677 / 500000000)) (hi := (21157071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555791627321 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555791627321 / 500000000000) = 1/(250000000000 / 555791627321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (399466267 / 500000000) (99866567 / 125000000) (Real.log (555791627321 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (555791627321 / 250000000000) = -Real.log (250000000000 / 555791627321) := by
    rw [show ((555791627321 / 250000000000) : ℝ) = ((250000000000 / 555791627321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (400150963 / 500000000) ≤ -Real.log (250000000000 / 556553245117) ∧
    -Real.log (250000000000 / 556553245117) ≤ (100037741 / 125000000) := by
  have h := checkLog_sound (w := (56553245117 / 1056553245117)) (n := 12)
    (lo := (53577373 / 500000000)) (hi := (107154747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556553245117 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556553245117 / 500000000000) = 1/(250000000000 / 556553245117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (400150963 / 500000000) (100037741 / 125000000) (Real.log (556553245117 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (556553245117 / 250000000000) = -Real.log (250000000000 / 556553245117) := by
    rw [show ((556553245117 / 250000000000) : ℝ) = ((250000000000 / 556553245117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (69230787 / 125000000) ≤ -Real.log (125000000000 / 217491557583) ∧
    -Real.log (125000000000 / 217491557583) ≤ (553846297 / 1000000000) := by
  have h := checkLog_sound (w := (92491557583 / 342491557583)) (n := 12)
    (lo := (69230787 / 125000000)) (hi := (553846297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217491557583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217491557583 / 125000000000) = 1/(125000000000 / 217491557583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69230787 / 125000000) (553846297 / 1000000000) (Real.log (217491557583 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (217491557583 / 125000000000) = -Real.log (125000000000 / 217491557583) := by
    rw [show ((217491557583 / 125000000000) : ℝ) = ((125000000000 / 217491557583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (554761119 / 1000000000) ≤ -Real.log (500000000000 / 870762459203) ∧
    -Real.log (500000000000 / 870762459203) ≤ (3467257 / 6250000) := by
  have h := checkLog_sound (w := (370762459203 / 1370762459203)) (n := 12)
    (lo := (554761119 / 1000000000)) (hi := (3467257 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870762459203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870762459203 / 500000000000) = 1/(500000000000 / 870762459203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (554761119 / 1000000000) (3467257 / 6250000) (Real.log (870762459203 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (870762459203 / 500000000000) = -Real.log (500000000000 / 870762459203) := by
    rw [show ((870762459203 / 500000000000) : ℝ) = ((500000000000 / 870762459203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (39484089 / 100000000) ≤ -Real.log (50000000000 / 74207401519) ∧
    -Real.log (50000000000 / 74207401519) ≤ (394840891 / 1000000000) := by
  have h := checkLog_sound (w := (24207401519 / 124207401519)) (n := 12)
    (lo := (39484089 / 100000000)) (hi := (394840891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74207401519 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74207401519 / 50000000000) = 1/(50000000000 / 74207401519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (39484089 / 100000000) (394840891 / 1000000000) (Real.log (74207401519 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (74207401519 / 50000000000) = -Real.log (50000000000 / 74207401519) := by
    rw [show ((74207401519 / 50000000000) : ℝ) = ((50000000000 / 74207401519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79100409 / 200000000) ≤ -Real.log (500000000000 / 742564802861) ∧
    -Real.log (500000000000 / 742564802861) ≤ (197751023 / 500000000) := by
  have h := checkLog_sound (w := (242564802861 / 1242564802861)) (n := 12)
    (lo := (79100409 / 200000000)) (hi := (197751023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742564802861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742564802861 / 500000000000) = 1/(500000000000 / 742564802861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79100409 / 200000000) (197751023 / 500000000) (Real.log (742564802861 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (742564802861 / 500000000000) = -Real.log (500000000000 / 742564802861) := by
    rw [show ((742564802861 / 500000000000) : ℝ) = ((500000000000 / 742564802861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1942661 / 50000000) ≤ -Real.log (961891884631 / 1000000000000) ∧
    -Real.log (961891884631 / 1000000000000) ≤ (38853221 / 1000000000) := by
  have h := checkLog_sound (w := (38108115369 / 1961891884631)) (n := 12)
    (lo := (1942661 / 50000000)) (hi := (38853221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961891884631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961891884631) = 1/(961891884631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38853221 / 1000000000) (-1942661 / 50000000) (Real.log (961891884631 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38724259 / 1000000000) ≤ -Real.log (38480637559 / 40000000000) ∧
    -Real.log (38480637559 / 40000000000) ≤ (1936213 / 50000000) := by
  have h := checkLog_sound (w := (1519362441 / 78480637559)) (n := 12)
    (lo := (38724259 / 1000000000)) (hi := (1936213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38480637559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38480637559) = 1/(38480637559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1936213 / 50000000) (-38724259 / 1000000000) (Real.log (38480637559 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell221

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell222Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell222
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

theorem reflection_log_1_neg : (80641147 / 250000000) ≤ -Real.log (5120 / 7069) ∧
    -Real.log (5120 / 7069) ≤ (322564589 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 12189)) (n := 12)
    (lo := (80641147 / 250000000)) (hi := (322564589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7069 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7069 / 5120) = 1/(5120 / 7069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80641147 / 250000000) (322564589 / 1000000000) (Real.log (7069 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7069 / 5120) = -Real.log (5120 / 7069) := by
    rw [show ((7069 / 5120) : ℝ) = ((5120 / 7069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (479107443 / 1000000000) ≤ -Real.log (3171 / 5120) ∧
    -Real.log (3171 / 5120) ≤ (119776861 / 250000000) := by
  have h := checkLog_sound (w := (1949 / 8291)) (n := 12)
    (lo := (479107443 / 1000000000)) (hi := (119776861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3171) = 1/(3171 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-119776861 / 250000000) (-479107443 / 1000000000) (Real.log (3171 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (322140109 / 1000000000) ≤ -Real.log (2560 / 3533) ∧
    -Real.log (2560 / 3533) ≤ (32214011 / 100000000) := by
  have h := checkLog_sound (w := (973 / 6093)) (n := 12)
    (lo := (322140109 / 1000000000)) (hi := (32214011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3533 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3533 / 2560) = 1/(2560 / 3533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (322140109 / 1000000000) (32214011 / 100000000) (Real.log (3533 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3533 / 2560) = -Real.log (2560 / 3533) := by
    rw [show ((3533 / 2560) : ℝ) = ((2560 / 3533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (59770227 / 125000000) ≤ -Real.log (1587 / 2560) ∧
    -Real.log (1587 / 2560) ≤ (478161817 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 4147)) (n := 12)
    (lo := (59770227 / 125000000)) (hi := (478161817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1587) = 1/(1587 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-478161817 / 1000000000) (-59770227 / 125000000) (Real.log (1587 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239393207 / 1000000000) ≤ -Real.log (500000 / 635239) ∧
    -Real.log (500000 / 635239) ≤ (29924151 / 125000000) := by
  have h := checkLog_sound (w := (135239 / 1135239)) (n := 12)
    (lo := (239393207 / 1000000000)) (hi := (29924151 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635239 / 500000) = 1/(500000 / 635239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239393207 / 1000000000) (29924151 / 125000000) (Real.log (635239 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (635239 / 500000) = -Real.log (500000 / 635239) := by
    rw [show ((635239 / 500000) : ℝ) = ((500000 / 635239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (315365753 / 1000000000) ≤ -Real.log (364761 / 500000) ∧
    -Real.log (364761 / 500000) ≤ (157682877 / 500000000) := by
  have h := checkLog_sound (w := (135239 / 864761)) (n := 12)
    (lo := (315365753 / 1000000000)) (hi := (157682877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364761) = 1/(364761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-157682877 / 500000000) (-315365753 / 1000000000) (Real.log (364761 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59931721 / 250000000) ≤ -Real.log (500000 / 635451) ∧
    -Real.log (500000 / 635451) ≤ (47945377 / 200000000) := by
  have h := checkLog_sound (w := (135451 / 1135451)) (n := 12)
    (lo := (59931721 / 250000000)) (hi := (47945377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635451 / 500000) = 1/(500000 / 635451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59931721 / 250000000) (47945377 / 200000000) (Real.log (635451 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (635451 / 500000) = -Real.log (500000 / 635451) := by
    rw [show ((635451 / 500000) : ℝ) = ((500000 / 635451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2527577 / 8000000) ≤ -Real.log (364549 / 500000) ∧
    -Real.log (364549 / 500000) ≤ (157973563 / 500000000) := by
  have h := checkLog_sound (w := (135451 / 864549)) (n := 12)
    (lo := (2527577 / 8000000)) (hi := (157973563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364549) = 1/(364549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-157973563 / 500000000) (-2527577 / 8000000) (Real.log (364549 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7132943 / 40000000) ≤ -Real.log (250000 / 298803) ∧
    -Real.log (250000 / 298803) ≤ (22290447 / 125000000) := by
  have h := checkLog_sound (w := (48803 / 548803)) (n := 12)
    (lo := (7132943 / 40000000)) (hi := (22290447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298803 / 250000) = 1/(250000 / 298803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7132943 / 40000000) (22290447 / 125000000) (Real.log (298803 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (298803 / 250000) = -Real.log (250000 / 298803) := by
    rw [show ((298803 / 250000) : ℝ) = ((250000 / 298803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21717639 / 100000000) ≤ -Real.log (201197 / 250000) ∧
    -Real.log (201197 / 250000) ≤ (217176391 / 1000000000) := by
  have h := checkLog_sound (w := (48803 / 451197)) (n := 12)
    (lo := (21717639 / 100000000)) (hi := (217176391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201197) = 1/(201197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-217176391 / 1000000000) (-21717639 / 100000000) (Real.log (201197 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89295219 / 500000000) ≤ -Real.log (1000000 / 1195531) ∧
    -Real.log (1000000 / 1195531) ≤ (178590439 / 1000000000) := by
  have h := checkLog_sound (w := (195531 / 2195531)) (n := 12)
    (lo := (89295219 / 500000000)) (hi := (178590439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195531 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195531 / 1000000) = 1/(1000000 / 1195531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89295219 / 500000000) (178590439 / 1000000000) (Real.log (1195531 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195531 / 1000000) = -Real.log (1000000 / 1195531) := by
    rw [show ((1195531 / 1000000) : ℝ) = ((1000000 / 1195531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (108786423 / 500000000) ≤ -Real.log (804469 / 1000000) ∧
    -Real.log (804469 / 1000000) ≤ (217572847 / 1000000000) := by
  have h := checkLog_sound (w := (195531 / 1804469)) (n := 12)
    (lo := (108786423 / 500000000)) (hi := (217572847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804469) = 1/(804469 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217572847 / 1000000000) (-108786423 / 500000000) (Real.log (804469 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (400150963 / 500000000) ≤ -Real.log (500000000000 / 1113106490233) ∧
    -Real.log (500000000000 / 1113106490233) ≤ (100037741 / 125000000) := by
  have h := checkLog_sound (w := (113106490233 / 2113106490233)) (n := 12)
    (lo := (53577373 / 500000000)) (hi := (107154747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113106490233 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1113106490233 / 1000000000000) = 1/(500000000000 / 1113106490233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (400150963 / 500000000) (100037741 / 125000000) (Real.log (1113106490233 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1113106490233 / 500000000000) = -Real.log (500000000000 / 1113106490233) := by
    rw [show ((1113106490233 / 500000000000) : ℝ) = ((500000000000 / 1113106490233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (801672031 / 1000000000) ≤ -Real.log (500000000000 / 1114632608011) ∧
    -Real.log (500000000000 / 1114632608011) ≤ (801672033 / 1000000000) := by
  have h := checkLog_sound (w := (114632608011 / 2114632608011)) (n := 12)
    (lo := (108524851 / 1000000000)) (hi := (27131213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114632608011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1114632608011 / 1000000000000) = 1/(500000000000 / 1114632608011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (801672031 / 1000000000) (801672033 / 1000000000) (Real.log (1114632608011 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1114632608011 / 500000000000) = -Real.log (500000000000 / 1114632608011) := by
    rw [show ((1114632608011 / 500000000000) : ℝ) = ((500000000000 / 1114632608011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (554758961 / 1000000000) ≤ -Real.log (100000000000 / 174152116043) ∧
    -Real.log (100000000000 / 174152116043) ≤ (277379481 / 500000000) := by
  have h := checkLog_sound (w := (74152116043 / 274152116043)) (n := 12)
    (lo := (554758961 / 1000000000)) (hi := (277379481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174152116043 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174152116043 / 100000000000) = 1/(100000000000 / 174152116043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (554758961 / 1000000000) (277379481 / 500000000) (Real.log (174152116043 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (174152116043 / 100000000000) = -Real.log (100000000000 / 174152116043) := by
    rw [show ((174152116043 / 100000000000) : ℝ) = ((100000000000 / 174152116043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (555674009 / 1000000000) ≤ -Real.log (25000000000 / 43577886649) ∧
    -Real.log (25000000000 / 43577886649) ≤ (55567401 / 100000000) := by
  have h := checkLog_sound (w := (18577886649 / 68577886649)) (n := 12)
    (lo := (555674009 / 1000000000)) (hi := (55567401 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43577886649 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43577886649 / 25000000000) = 1/(25000000000 / 43577886649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (555674009 / 1000000000) (55567401 / 100000000) (Real.log (43577886649 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (43577886649 / 25000000000) = -Real.log (25000000000 / 43577886649) := by
    rw [show ((43577886649 / 25000000000) : ℝ) = ((25000000000 / 43577886649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79099993 / 200000000) ≤ -Real.log (100000000000 / 148512651779) ∧
    -Real.log (100000000000 / 148512651779) ≤ (197749983 / 500000000) := by
  have h := checkLog_sound (w := (48512651779 / 248512651779)) (n := 12)
    (lo := (79099993 / 200000000)) (hi := (197749983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148512651779 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148512651779 / 100000000000) = 1/(100000000000 / 148512651779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79099993 / 200000000) (197749983 / 500000000) (Real.log (148512651779 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (148512651779 / 100000000000) = -Real.log (100000000000 / 148512651779) := by
    rw [show ((148512651779 / 100000000000) : ℝ) = ((100000000000 / 148512651779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (99040821 / 250000000) ≤ -Real.log (25000000000 / 37152798927) ∧
    -Real.log (25000000000 / 37152798927) ≤ (79232657 / 200000000) := by
  have h := checkLog_sound (w := (12152798927 / 62152798927)) (n := 12)
    (lo := (99040821 / 250000000)) (hi := (79232657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37152798927 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37152798927 / 25000000000) = 1/(25000000000 / 37152798927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (99040821 / 250000000) (79232657 / 200000000) (Real.log (37152798927 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37152798927 / 25000000000) = -Real.log (25000000000 / 37152798927) := by
    rw [show ((37152798927 / 25000000000) : ℝ) = ((25000000000 / 37152798927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4872801 / 125000000) ≤ -Real.log (961767628039 / 1000000000000) ∧
    -Real.log (961767628039 / 1000000000000) ≤ (38982409 / 1000000000) := by
  have h := checkLog_sound (w := (38232371961 / 1961767628039)) (n := 12)
    (lo := (4872801 / 125000000)) (hi := (38982409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961767628039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961767628039) = 1/(961767628039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38982409 / 1000000000) (-4872801 / 125000000) (Real.log (961767628039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19426407 / 500000000) ≤ -Real.log (60118267191 / 62500000000) ∧
    -Real.log (60118267191 / 62500000000) ≤ (7770563 / 200000000) := by
  have h := checkLog_sound (w := (2381732809 / 122618267191)) (n := 12)
    (lo := (19426407 / 500000000)) (hi := (7770563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60118267191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60118267191) = 1/(60118267191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7770563 / 200000000) (-19426407 / 500000000) (Real.log (60118267191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell222

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell223Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell223
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

theorem reflection_log_1_neg : (161494443 / 500000000) ≤ -Real.log (160 / 221) ∧
    -Real.log (160 / 221) ≤ (322988887 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 381)) (n := 12)
    (lo := (161494443 / 500000000)) (hi := (322988887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221 / 160) = 1/(160 / 221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (161494443 / 500000000) (322988887 / 1000000000) (Real.log (221 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (221 / 160) = -Real.log (160 / 221) := by
    rw [show ((221 / 160) : ℝ) = ((160 / 221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (96010793 / 200000000) ≤ -Real.log (99 / 160) ∧
    -Real.log (99 / 160) ≤ (240026983 / 500000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 99) = 1/(99 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240026983 / 500000000) (-96010793 / 200000000) (Real.log (99 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80641147 / 250000000) ≤ -Real.log (5120 / 7069) ∧
    -Real.log (5120 / 7069) ≤ (322564589 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 12189)) (n := 12)
    (lo := (80641147 / 250000000)) (hi := (322564589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7069 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7069 / 5120) = 1/(5120 / 7069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80641147 / 250000000) (322564589 / 1000000000) (Real.log (7069 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7069 / 5120) = -Real.log (5120 / 7069) := by
    rw [show ((7069 / 5120) : ℝ) = ((5120 / 7069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (479107443 / 1000000000) ≤ -Real.log (3171 / 5120) ∧
    -Real.log (3171 / 5120) ≤ (119776861 / 250000000) := by
  have h := checkLog_sound (w := (1949 / 8291)) (n := 12)
    (lo := (479107443 / 1000000000)) (hi := (119776861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3171) = 1/(3171 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-119776861 / 250000000) (-479107443 / 1000000000) (Real.log (3171 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239726097 / 1000000000) ≤ -Real.log (1000000 / 1270901) ∧
    -Real.log (1000000 / 1270901) ≤ (119863049 / 500000000) := by
  have h := checkLog_sound (w := (270901 / 2270901)) (n := 12)
    (lo := (239726097 / 1000000000)) (hi := (119863049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270901 / 1000000) = 1/(1000000 / 1270901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239726097 / 1000000000) (119863049 / 500000000) (Real.log (1270901 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1270901 / 1000000) = -Real.log (1000000 / 1270901) := by
    rw [show ((1270901 / 1000000) : ℝ) = ((1000000 / 1270901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (315945753 / 1000000000) ≤ -Real.log (729099 / 1000000) ∧
    -Real.log (729099 / 1000000) ≤ (157972877 / 500000000) := by
  have h := checkLog_sound (w := (270901 / 1729099)) (n := 12)
    (lo := (315945753 / 1000000000)) (hi := (157972877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729099) = 1/(729099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-157972877 / 500000000) (-315945753 / 1000000000) (Real.log (729099 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240058877 / 1000000000) ≤ -Real.log (250000 / 317831) ∧
    -Real.log (250000 / 317831) ≤ (120029439 / 500000000) := by
  have h := checkLog_sound (w := (67831 / 567831)) (n := 12)
    (lo := (240058877 / 1000000000)) (hi := (120029439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317831 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317831 / 250000) = 1/(250000 / 317831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240058877 / 1000000000) (120029439 / 500000000) (Real.log (317831 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (317831 / 250000) = -Real.log (250000 / 317831) := by
    rw [show ((317831 / 250000) : ℝ) = ((250000 / 317831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31652609 / 100000000) ≤ -Real.log (182169 / 250000) ∧
    -Real.log (182169 / 250000) ≤ (316526091 / 1000000000) := by
  have h := checkLog_sound (w := (67831 / 432169)) (n := 12)
    (lo := (31652609 / 100000000)) (hi := (316526091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 182169) = 1/(182169 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-316526091 / 1000000000) (-31652609 / 100000000) (Real.log (182169 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178589601 / 1000000000) ≤ -Real.log (100000 / 119553) ∧
    -Real.log (100000 / 119553) ≤ (89294801 / 500000000) := by
  have h := checkLog_sound (w := (19553 / 219553)) (n := 12)
    (lo := (178589601 / 1000000000)) (hi := (89294801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119553 / 100000) = 1/(100000 / 119553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178589601 / 1000000000) (89294801 / 500000000) (Real.log (119553 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119553 / 100000) = -Real.log (100000 / 119553) := by
    rw [show ((119553 / 100000) : ℝ) = ((100000 / 119553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (217571603 / 1000000000) ≤ -Real.log (80447 / 100000) ∧
    -Real.log (80447 / 100000) ≤ (54392901 / 250000000) := by
  have h := checkLog_sound (w := (19553 / 180447)) (n := 12)
    (lo := (217571603 / 1000000000)) (hi := (54392901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80447) = 1/(80447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-54392901 / 250000000) (-217571603 / 1000000000) (Real.log (80447 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (178856393 / 1000000000) ≤ -Real.log (1000000 / 1195849) ∧
    -Real.log (1000000 / 1195849) ≤ (89428197 / 500000000) := by
  have h := checkLog_sound (w := (195849 / 2195849)) (n := 12)
    (lo := (178856393 / 1000000000)) (hi := (89428197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195849 / 1000000) = 1/(1000000 / 1195849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (178856393 / 1000000000) (89428197 / 500000000) (Real.log (1195849 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195849 / 1000000) = -Real.log (1000000 / 1195849) := by
    rw [show ((1195849 / 1000000) : ℝ) = ((1000000 / 1195849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27246027 / 125000000) ≤ -Real.log (804151 / 1000000) ∧
    -Real.log (804151 / 1000000) ≤ (217968217 / 1000000000) := by
  have h := checkLog_sound (w := (195849 / 1804151)) (n := 12)
    (lo := (27246027 / 125000000)) (hi := (217968217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804151) = 1/(804151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217968217 / 1000000000) (-27246027 / 125000000) (Real.log (804151 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (801672031 / 1000000000) ≤ -Real.log (50000000000 / 111463260801) ∧
    -Real.log (50000000000 / 111463260801) ≤ (801672033 / 1000000000) := by
  have h := checkLog_sound (w := (11463260801 / 211463260801)) (n := 12)
    (lo := (108524851 / 1000000000)) (hi := (27131213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111463260801 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(111463260801 / 100000000000) = 1/(50000000000 / 111463260801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (801672031 / 1000000000) (801672033 / 1000000000) (Real.log (111463260801 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (111463260801 / 50000000000) = -Real.log (50000000000 / 111463260801) := by
    rw [show ((111463260801 / 50000000000) : ℝ) = ((50000000000 / 111463260801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16060857 / 20000000) ≤ -Real.log (250000000000 / 558080808081) ∧
    -Real.log (250000000000 / 558080808081) ≤ (200760713 / 250000000) := by
  have h := checkLog_sound (w := (58080808081 / 1058080808081)) (n := 12)
    (lo := (10989567 / 100000000)) (hi := (109895671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558080808081 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558080808081 / 500000000000) = 1/(250000000000 / 558080808081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (16060857 / 20000000) (200760713 / 250000000) (Real.log (558080808081 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (558080808081 / 250000000000) = -Real.log (250000000000 / 558080808081) := by
    rw [show ((558080808081 / 250000000000) : ℝ) = ((250000000000 / 558080808081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (555671851 / 1000000000) ≤ -Real.log (500000000000 / 871555851811) ∧
    -Real.log (500000000000 / 871555851811) ≤ (138917963 / 250000000) := by
  have h := checkLog_sound (w := (371555851811 / 1371555851811)) (n := 12)
    (lo := (555671851 / 1000000000)) (hi := (138917963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871555851811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871555851811 / 500000000000) = 1/(500000000000 / 871555851811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (555671851 / 1000000000) (138917963 / 250000000) (Real.log (871555851811 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (871555851811 / 500000000000) = -Real.log (500000000000 / 871555851811) := by
    rw [show ((871555851811 / 500000000000) : ℝ) = ((500000000000 / 871555851811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (556584967 / 1000000000) ≤ -Real.log (250000000000 / 436176023363) ∧
    -Real.log (250000000000 / 436176023363) ≤ (69573121 / 125000000) := by
  have h := checkLog_sound (w := (186176023363 / 686176023363)) (n := 12)
    (lo := (556584967 / 1000000000)) (hi := (69573121 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436176023363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436176023363 / 250000000000) = 1/(250000000000 / 436176023363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (556584967 / 1000000000) (69573121 / 125000000) (Real.log (436176023363 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (436176023363 / 250000000000) = -Real.log (250000000000 / 436176023363) := by
    rw [show ((436176023363 / 250000000000) : ℝ) = ((250000000000 / 436176023363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79232241 / 200000000) ≤ -Real.log (500000000000 / 743054433353) ∧
    -Real.log (500000000000 / 743054433353) ≤ (198080603 / 500000000) := by
  have h := checkLog_sound (w := (243054433353 / 1243054433353)) (n := 12)
    (lo := (79232241 / 200000000)) (hi := (198080603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743054433353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743054433353 / 500000000000) = 1/(500000000000 / 743054433353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79232241 / 200000000) (198080603 / 500000000) (Real.log (743054433353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (743054433353 / 500000000000) = -Real.log (500000000000 / 743054433353) := by
    rw [show ((743054433353 / 500000000000) : ℝ) = ((500000000000 / 743054433353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (396824609 / 1000000000) ≤ -Real.log (15625000000 / 23235860709) ∧
    -Real.log (15625000000 / 23235860709) ≤ (39682461 / 100000000) := by
  have h := checkLog_sound (w := (7610860709 / 38860860709)) (n := 12)
    (lo := (396824609 / 1000000000)) (hi := (39682461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23235860709 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23235860709 / 15625000000) = 1/(15625000000 / 23235860709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (396824609 / 1000000000) (39682461 / 100000000) (Real.log (23235860709 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23235860709 / 15625000000) = -Real.log (15625000000 / 23235860709) := by
    rw [show ((23235860709 / 15625000000) : ℝ) = ((15625000000 / 23235860709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39111823 / 1000000000) ≤ -Real.log (961643169199 / 1000000000000) ∧
    -Real.log (961643169199 / 1000000000000) ≤ (2444489 / 62500000) := by
  have h := checkLog_sound (w := (38356830801 / 1961643169199)) (n := 12)
    (lo := (39111823 / 1000000000)) (hi := (2444489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961643169199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961643169199) = 1/(961643169199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2444489 / 62500000) (-39111823 / 1000000000) (Real.log (961643169199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38982001 / 1000000000) ≤ -Real.log (9617680191 / 10000000000) ∧
    -Real.log (9617680191 / 10000000000) ≤ (19491001 / 500000000) := by
  have h := checkLog_sound (w := (382319809 / 19617680191)) (n := 12)
    (lo := (38982001 / 1000000000)) (hi := (19491001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9617680191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9617680191) = 1/(9617680191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19491001 / 500000000) (-38982001 / 1000000000) (Real.log (9617680191 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell223

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell224Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell224
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

theorem reflection_log_1_neg : (80853251 / 250000000) ≤ -Real.log (1024 / 1415) ∧
    -Real.log (1024 / 1415) ≤ (64682601 / 200000000) := by
  have h := checkLog_sound (w := (391 / 2439)) (n := 12)
    (lo := (80853251 / 250000000)) (hi := (64682601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415 / 1024) = 1/(1024 / 1415) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80853251 / 250000000) (64682601 / 200000000) (Real.log (1415 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1415 / 1024) = -Real.log (1024 / 1415) := by
    rw [show ((1415 / 1024) : ℝ) = ((1024 / 1415) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (481001383 / 1000000000) ≤ -Real.log (633 / 1024) ∧
    -Real.log (633 / 1024) ≤ (60125173 / 125000000) := by
  have h := checkLog_sound (w := (391 / 1657)) (n := 12)
    (lo := (481001383 / 1000000000)) (hi := (60125173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 633) = 1/(633 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60125173 / 125000000) (-481001383 / 1000000000) (Real.log (633 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (161494443 / 500000000) ≤ -Real.log (160 / 221) ∧
    -Real.log (160 / 221) ≤ (322988887 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 381)) (n := 12)
    (lo := (161494443 / 500000000)) (hi := (322988887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221 / 160) = 1/(160 / 221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (161494443 / 500000000) (322988887 / 1000000000) (Real.log (221 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (221 / 160) = -Real.log (160 / 221) := by
    rw [show ((221 / 160) : ℝ) = ((160 / 221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (96010793 / 200000000) ≤ -Real.log (99 / 160) ∧
    -Real.log (99 / 160) ≤ (240026983 / 500000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 99) = 1/(99 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240026983 / 500000000) (-96010793 / 200000000) (Real.log (99 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24005809 / 100000000) ≤ -Real.log (1000000 / 1271323) ∧
    -Real.log (1000000 / 1271323) ≤ (240058091 / 1000000000) := by
  have h := checkLog_sound (w := (271323 / 2271323)) (n := 12)
    (lo := (24005809 / 100000000)) (hi := (240058091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271323 / 1000000) = 1/(1000000 / 1271323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24005809 / 100000000) (240058091 / 1000000000) (Real.log (1271323 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1271323 / 1000000) = -Real.log (1000000 / 1271323) := by
    rw [show ((1271323 / 1000000) : ℝ) = ((1000000 / 1271323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316524717 / 1000000000) ≤ -Real.log (728677 / 1000000) ∧
    -Real.log (728677 / 1000000) ≤ (158262359 / 500000000) := by
  have h := checkLog_sound (w := (271323 / 1728677)) (n := 12)
    (lo := (316524717 / 1000000000)) (hi := (158262359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728677) = 1/(728677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158262359 / 500000000) (-316524717 / 1000000000) (Real.log (728677 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48078309 / 200000000) ≤ -Real.log (1000000 / 1271747) ∧
    -Real.log (1000000 / 1271747) ≤ (120195773 / 500000000) := by
  have h := checkLog_sound (w := (271747 / 2271747)) (n := 12)
    (lo := (48078309 / 200000000)) (hi := (120195773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271747 / 1000000) = 1/(1000000 / 1271747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48078309 / 200000000) (120195773 / 500000000) (Real.log (1271747 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1271747 / 1000000) = -Real.log (1000000 / 1271747) := by
    rw [show ((1271747 / 1000000) : ℝ) = ((1000000 / 1271747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (317106763 / 1000000000) ≤ -Real.log (728253 / 1000000) ∧
    -Real.log (728253 / 1000000) ≤ (79276691 / 250000000) := by
  have h := checkLog_sound (w := (271747 / 1728253)) (n := 12)
    (lo := (317106763 / 1000000000)) (hi := (79276691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728253) = 1/(728253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-79276691 / 250000000) (-317106763 / 1000000000) (Real.log (728253 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178855557 / 1000000000) ≤ -Real.log (125000 / 149481) ∧
    -Real.log (125000 / 149481) ≤ (89427779 / 500000000) := by
  have h := checkLog_sound (w := (24481 / 274481)) (n := 12)
    (lo := (178855557 / 1000000000)) (hi := (89427779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149481 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149481 / 125000) = 1/(125000 / 149481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178855557 / 1000000000) (89427779 / 500000000) (Real.log (149481 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (149481 / 125000) = -Real.log (125000 / 149481) := by
    rw [show ((149481 / 125000) : ℝ) = ((125000 / 149481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54491743 / 250000000) ≤ -Real.log (100519 / 125000) ∧
    -Real.log (100519 / 125000) ≤ (217966973 / 1000000000) := by
  have h := checkLog_sound (w := (24481 / 225519)) (n := 12)
    (lo := (54491743 / 250000000)) (hi := (217966973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100519) = 1/(100519 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-217966973 / 1000000000) (-54491743 / 250000000) (Real.log (100519 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (179121441 / 1000000000) ≤ -Real.log (500000 / 598083) ∧
    -Real.log (500000 / 598083) ≤ (89560721 / 500000000) := by
  have h := checkLog_sound (w := (98083 / 1098083)) (n := 12)
    (lo := (179121441 / 1000000000)) (hi := (89560721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598083 / 500000) = 1/(500000 / 598083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (179121441 / 1000000000) (89560721 / 500000000) (Real.log (598083 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (598083 / 500000) = -Real.log (500000 / 598083) := by
    rw [show ((598083 / 500000) : ℝ) = ((500000 / 598083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109181249 / 500000000) ≤ -Real.log (401917 / 500000) ∧
    -Real.log (401917 / 500000) ≤ (218362499 / 1000000000) := by
  have h := checkLog_sound (w := (98083 / 901917)) (n := 12)
    (lo := (109181249 / 500000000)) (hi := (218362499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401917) = 1/(401917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-218362499 / 1000000000) (-109181249 / 500000000) (Real.log (401917 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16060857 / 20000000) ≤ -Real.log (500000000000 / 1116161616161) ∧
    -Real.log (500000000000 / 1116161616161) ≤ (200760713 / 250000000) := by
  have h := checkLog_sound (w := (116161616161 / 2116161616161)) (n := 12)
    (lo := (10989567 / 100000000)) (hi := (109895671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116161616161 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1116161616161 / 1000000000000) = 1/(500000000000 / 1116161616161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16060857 / 20000000) (200760713 / 250000000) (Real.log (1116161616161 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1116161616161 / 500000000000) = -Real.log (500000000000 / 1116161616161) := by
    rw [show ((1116161616161 / 500000000000) : ℝ) = ((500000000000 / 1116161616161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (804414387 / 1000000000) ≤ -Real.log (500000000000 / 1117693522907) ∧
    -Real.log (500000000000 / 1117693522907) ≤ (804414389 / 1000000000) := by
  have h := checkLog_sound (w := (117693522907 / 2117693522907)) (n := 12)
    (lo := (111267207 / 1000000000)) (hi := (13908401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117693522907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1117693522907 / 1000000000000) = 1/(500000000000 / 1117693522907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (804414387 / 1000000000) (804414389 / 1000000000) (Real.log (1117693522907 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1117693522907 / 500000000000) = -Real.log (500000000000 / 1117693522907) := by
    rw [show ((1117693522907 / 500000000000) : ℝ) = ((500000000000 / 1117693522907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (69572851 / 125000000) ≤ -Real.log (250000000000 / 436175081689) ∧
    -Real.log (250000000000 / 436175081689) ≤ (556582809 / 1000000000) := by
  have h := checkLog_sound (w := (186175081689 / 686175081689)) (n := 12)
    (lo := (69572851 / 125000000)) (hi := (556582809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436175081689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436175081689 / 250000000000) = 1/(250000000000 / 436175081689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69572851 / 125000000) (556582809 / 1000000000) (Real.log (436175081689 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (436175081689 / 250000000000) = -Real.log (250000000000 / 436175081689) := by
    rw [show ((436175081689 / 250000000000) : ℝ) = ((250000000000 / 436175081689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (557498309 / 1000000000) ≤ -Real.log (62500000000 / 109143645821) ∧
    -Real.log (62500000000 / 109143645821) ≤ (55749831 / 100000000) := by
  have h := checkLog_sound (w := (46643645821 / 171643645821)) (n := 12)
    (lo := (557498309 / 1000000000)) (hi := (55749831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109143645821 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109143645821 / 62500000000) = 1/(62500000000 / 109143645821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (557498309 / 1000000000) (55749831 / 100000000) (Real.log (109143645821 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (109143645821 / 62500000000) = -Real.log (62500000000 / 109143645821) := by
    rw [show ((109143645821 / 62500000000) : ℝ) = ((62500000000 / 109143645821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (39682253 / 100000000) ≤ -Real.log (500000000000 / 743545996279) ∧
    -Real.log (500000000000 / 743545996279) ≤ (396822531 / 1000000000) := by
  have h := checkLog_sound (w := (243545996279 / 1243545996279)) (n := 12)
    (lo := (39682253 / 100000000)) (hi := (396822531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743545996279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743545996279 / 500000000000) = 1/(500000000000 / 743545996279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (39682253 / 100000000) (396822531 / 1000000000) (Real.log (743545996279 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (743545996279 / 500000000000) = -Real.log (500000000000 / 743545996279) := by
    rw [show ((743545996279 / 500000000000) : ℝ) = ((500000000000 / 743545996279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (19874197 / 50000000) ≤ -Real.log (250000000000 / 372018974067) ∧
    -Real.log (250000000000 / 372018974067) ≤ (397483941 / 1000000000) := by
  have h := checkLog_sound (w := (122018974067 / 622018974067)) (n := 12)
    (lo := (19874197 / 50000000)) (hi := (397483941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372018974067 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372018974067 / 250000000000) = 1/(250000000000 / 372018974067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (19874197 / 50000000) (397483941 / 1000000000) (Real.log (372018974067 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (372018974067 / 250000000000) = -Real.log (250000000000 / 372018974067) := by
    rw [show ((372018974067 / 250000000000) : ℝ) = ((250000000000 / 372018974067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1226283 / 31250000) ≤ -Real.log (240379725111 / 250000000000) ∧
    -Real.log (240379725111 / 250000000000) ≤ (39241057 / 1000000000) := by
  have h := checkLog_sound (w := (9620274889 / 490379725111)) (n := 12)
    (lo := (1226283 / 31250000)) (hi := (39241057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240379725111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240379725111) = 1/(240379725111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-39241057 / 1000000000) (-1226283 / 31250000) (Real.log (240379725111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7822283 / 200000000) ≤ -Real.log (15025680639 / 15625000000) ∧
    -Real.log (15025680639 / 15625000000) ≤ (4888927 / 125000000) := by
  have h := checkLog_sound (w := (599319361 / 30650680639)) (n := 12)
    (lo := (7822283 / 200000000)) (hi := (4888927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15025680639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15025680639) = 1/(15025680639 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4888927 / 125000000) (-7822283 / 200000000) (Real.log (15025680639 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell224

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell225Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell225
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

theorem reflection_log_1_neg : (161918471 / 500000000) ≤ -Real.log (2560 / 3539) ∧
    -Real.log (2560 / 3539) ≤ (323836943 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 6099)) (n := 12)
    (lo := (161918471 / 500000000)) (hi := (323836943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3539 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3539 / 2560) = 1/(2560 / 3539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (161918471 / 500000000) (323836943 / 1000000000) (Real.log (3539 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3539 / 2560) = -Real.log (2560 / 3539) := by
    rw [show ((3539 / 2560) : ℝ) = ((2560 / 3539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4819497 / 10000000) ≤ -Real.log (1581 / 2560) ∧
    -Real.log (1581 / 2560) ≤ (481949701 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 4141)) (n := 12)
    (lo := (4819497 / 10000000)) (hi := (481949701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1581) = 1/(1581 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-481949701 / 1000000000) (-4819497 / 10000000) (Real.log (1581 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80853251 / 250000000) ≤ -Real.log (1024 / 1415) ∧
    -Real.log (1024 / 1415) ≤ (64682601 / 200000000) := by
  have h := checkLog_sound (w := (391 / 2439)) (n := 12)
    (lo := (80853251 / 250000000)) (hi := (64682601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415 / 1024) = 1/(1024 / 1415) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80853251 / 250000000) (64682601 / 200000000) (Real.log (1415 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1415 / 1024) = -Real.log (1024 / 1415) := by
    rw [show ((1415 / 1024) : ℝ) = ((1024 / 1415) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (481001383 / 1000000000) ≤ -Real.log (633 / 1024) ∧
    -Real.log (633 / 1024) ≤ (60125173 / 125000000) := by
  have h := checkLog_sound (w := (391 / 1657)) (n := 12)
    (lo := (481001383 / 1000000000)) (hi := (60125173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 633) = 1/(633 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60125173 / 125000000) (-481001383 / 1000000000) (Real.log (633 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240390759 / 1000000000) ≤ -Real.log (500000 / 635873) ∧
    -Real.log (500000 / 635873) ≤ (6009769 / 25000000) := by
  have h := checkLog_sound (w := (135873 / 1135873)) (n := 12)
    (lo := (240390759 / 1000000000)) (hi := (6009769 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635873 / 500000) = 1/(500000 / 635873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240390759 / 1000000000) (6009769 / 25000000) (Real.log (635873 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (635873 / 500000) = -Real.log (500000 / 635873) := by
    rw [show ((635873 / 500000) : ℝ) = ((500000 / 635873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31710539 / 100000000) ≤ -Real.log (364127 / 500000) ∧
    -Real.log (364127 / 500000) ≤ (317105391 / 1000000000) := by
  have h := checkLog_sound (w := (135873 / 864127)) (n := 12)
    (lo := (31710539 / 100000000)) (hi := (317105391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364127) = 1/(364127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317105391 / 1000000000) (-31710539 / 100000000) (Real.log (364127 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240724103 / 1000000000) ≤ -Real.log (100000 / 127217) ∧
    -Real.log (100000 / 127217) ≤ (30090513 / 125000000) := by
  have h := checkLog_sound (w := (27217 / 227217)) (n := 12)
    (lo := (240724103 / 1000000000)) (hi := (30090513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127217 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127217 / 100000) = 1/(100000 / 127217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240724103 / 1000000000) (30090513 / 125000000) (Real.log (127217 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127217 / 100000) = -Real.log (100000 / 127217) := by
    rw [show ((127217 / 100000) : ℝ) = ((100000 / 127217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158843887 / 500000000) ≤ -Real.log (72783 / 100000) ∧
    -Real.log (72783 / 100000) ≤ (12707511 / 40000000) := by
  have h := checkLog_sound (w := (27217 / 172783)) (n := 12)
    (lo := (158843887 / 500000000)) (hi := (12707511 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72783) = 1/(72783 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12707511 / 40000000) (-158843887 / 500000000) (Real.log (72783 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35824121 / 200000000) ≤ -Real.log (200000 / 239233) ∧
    -Real.log (200000 / 239233) ≤ (89560303 / 500000000) := by
  have h := checkLog_sound (w := (39233 / 439233)) (n := 12)
    (lo := (35824121 / 200000000)) (hi := (89560303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239233 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239233 / 200000) = 1/(200000 / 239233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35824121 / 200000000) (89560303 / 500000000) (Real.log (239233 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (239233 / 200000) = -Real.log (200000 / 239233) := by
    rw [show ((239233 / 200000) : ℝ) = ((200000 / 239233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (109180627 / 500000000) ≤ -Real.log (160767 / 200000) ∧
    -Real.log (160767 / 200000) ≤ (43672251 / 200000000) := by
  have h := checkLog_sound (w := (39233 / 360767)) (n := 12)
    (lo := (109180627 / 500000000)) (hi := (43672251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160767) = 1/(160767 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43672251 / 200000000) (-109180627 / 500000000) (Real.log (160767 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35877451 / 200000000) ≤ -Real.log (250000 / 299121) ∧
    -Real.log (250000 / 299121) ≤ (22423407 / 125000000) := by
  have h := checkLog_sound (w := (49121 / 549121)) (n := 12)
    (lo := (35877451 / 200000000)) (hi := (22423407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299121 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299121 / 250000) = 1/(250000 / 299121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35877451 / 200000000) (22423407 / 125000000) (Real.log (299121 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (299121 / 250000) = -Real.log (250000 / 299121) := by
    rw [show ((299121 / 250000) : ℝ) = ((250000 / 299121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (218758181 / 1000000000) ≤ -Real.log (200879 / 250000) ∧
    -Real.log (200879 / 250000) ≤ (109379091 / 500000000) := by
  have h := checkLog_sound (w := (49121 / 450879)) (n := 12)
    (lo := (218758181 / 1000000000)) (hi := (109379091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200879) = 1/(200879 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-109379091 / 500000000) (-218758181 / 1000000000) (Real.log (200879 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (804414387 / 1000000000) ≤ -Real.log (250000000000 / 558846761453) ∧
    -Real.log (250000000000 / 558846761453) ≤ (804414389 / 1000000000) := by
  have h := checkLog_sound (w := (58846761453 / 1058846761453)) (n := 12)
    (lo := (111267207 / 1000000000)) (hi := (13908401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558846761453 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558846761453 / 500000000000) = 1/(250000000000 / 558846761453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (804414387 / 1000000000) (804414389 / 1000000000) (Real.log (558846761453 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (558846761453 / 250000000000) = -Real.log (250000000000 / 558846761453) := by
    rw [show ((558846761453 / 250000000000) : ℝ) = ((250000000000 / 558846761453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (402893321 / 500000000) ≤ -Real.log (31250000000 / 69951771031) ∧
    -Real.log (31250000000 / 69951771031) ≤ (201446661 / 250000000) := by
  have h := checkLog_sound (w := (7451771031 / 132451771031)) (n := 12)
    (lo := (56319731 / 500000000)) (hi := (112639463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69951771031 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69951771031 / 62500000000) = 1/(31250000000 / 69951771031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (402893321 / 500000000) (201446661 / 250000000) (Real.log (69951771031 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (69951771031 / 31250000000) = -Real.log (31250000000 / 69951771031) := by
    rw [show ((69951771031 / 31250000000) : ℝ) = ((31250000000 / 69951771031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (557496149 / 1000000000) ≤ -Real.log (500000000000 / 873147281031) ∧
    -Real.log (500000000000 / 873147281031) ≤ (11149923 / 20000000) := by
  have h := checkLog_sound (w := (373147281031 / 1373147281031)) (n := 12)
    (lo := (557496149 / 1000000000)) (hi := (11149923 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873147281031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873147281031 / 500000000000) = 1/(500000000000 / 873147281031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (557496149 / 1000000000) (11149923 / 20000000) (Real.log (873147281031 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (873147281031 / 500000000000) = -Real.log (500000000000 / 873147281031) := by
    rw [show ((873147281031 / 500000000000) : ℝ) = ((500000000000 / 873147281031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279205939 / 500000000) ≤ -Real.log (500000000000 / 873947212949) ∧
    -Real.log (500000000000 / 873947212949) ≤ (558411879 / 1000000000) := by
  have h := checkLog_sound (w := (373947212949 / 1373947212949)) (n := 12)
    (lo := (279205939 / 500000000)) (hi := (558411879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873947212949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873947212949 / 500000000000) = 1/(500000000000 / 873947212949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (279205939 / 500000000) (558411879 / 1000000000) (Real.log (873947212949 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (873947212949 / 500000000000) = -Real.log (500000000000 / 873947212949) := by
    rw [show ((873947212949 / 500000000000) : ℝ) = ((500000000000 / 873947212949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (19874093 / 50000000) ≤ -Real.log (100000000000 / 148807280101) ∧
    -Real.log (100000000000 / 148807280101) ≤ (397481861 / 1000000000) := by
  have h := checkLog_sound (w := (48807280101 / 248807280101)) (n := 12)
    (lo := (19874093 / 50000000)) (hi := (397481861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148807280101 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148807280101 / 100000000000) = 1/(100000000000 / 148807280101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (19874093 / 50000000) (397481861 / 1000000000) (Real.log (148807280101 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (148807280101 / 100000000000) = -Real.log (100000000000 / 148807280101) := by
    rw [show ((148807280101 / 100000000000) : ℝ) = ((100000000000 / 148807280101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (398145437 / 1000000000) ≤ -Real.log (500000000000 / 744530289379) ∧
    -Real.log (500000000000 / 744530289379) ≤ (199072719 / 500000000) := by
  have h := checkLog_sound (w := (244530289379 / 1244530289379)) (n := 12)
    (lo := (398145437 / 1000000000)) (hi := (199072719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744530289379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744530289379 / 500000000000) = 1/(500000000000 / 744530289379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (398145437 / 1000000000) (199072719 / 500000000) (Real.log (744530289379 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (744530289379 / 500000000000) = -Real.log (500000000000 / 744530289379) := by
    rw [show ((744530289379 / 500000000000) : ℝ) = ((500000000000 / 744530289379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1574837 / 40000000) ≤ -Real.log (60087127359 / 62500000000) ∧
    -Real.log (60087127359 / 62500000000) ≤ (19685463 / 500000000) := by
  have h := checkLog_sound (w := (2412872641 / 122587127359)) (n := 12)
    (lo := (1574837 / 40000000)) (hi := (19685463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60087127359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60087127359) = 1/(60087127359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19685463 / 500000000) (-1574837 / 40000000) (Real.log (60087127359 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4905081 / 125000000) ≤ -Real.log (38460771711 / 40000000000) ∧
    -Real.log (38460771711 / 40000000000) ≤ (39240649 / 1000000000) := by
  have h := checkLog_sound (w := (1539228289 / 78460771711)) (n := 12)
    (lo := (4905081 / 125000000)) (hi := (39240649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38460771711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38460771711) = 1/(38460771711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-39240649 / 1000000000) (-4905081 / 125000000) (Real.log (38460771711 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell225

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell226Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell226
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

theorem reflection_log_1_neg : (324260701 / 1000000000) ≤ -Real.log (5120 / 7081) ∧
    -Real.log (5120 / 7081) ≤ (162130351 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 12201)) (n := 12)
    (lo := (324260701 / 1000000000)) (hi := (162130351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7081 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7081 / 5120) = 1/(5120 / 7081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324260701 / 1000000000) (162130351 / 500000000) (Real.log (7081 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7081 / 5120) = -Real.log (5120 / 7081) := by
    rw [show ((7081 / 5120) : ℝ) = ((5120 / 7081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (482898917 / 1000000000) ≤ -Real.log (3159 / 5120) ∧
    -Real.log (3159 / 5120) ≤ (241449459 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 8279)) (n := 12)
    (lo := (482898917 / 1000000000)) (hi := (241449459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3159) = 1/(3159 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-241449459 / 500000000) (-482898917 / 1000000000) (Real.log (3159 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (161918471 / 500000000) ≤ -Real.log (2560 / 3539) ∧
    -Real.log (2560 / 3539) ≤ (323836943 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 6099)) (n := 12)
    (lo := (161918471 / 500000000)) (hi := (323836943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3539 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3539 / 2560) = 1/(2560 / 3539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (161918471 / 500000000) (323836943 / 1000000000) (Real.log (3539 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3539 / 2560) = -Real.log (2560 / 3539) := by
    rw [show ((3539 / 2560) : ℝ) = ((2560 / 3539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4819497 / 10000000) ≤ -Real.log (1581 / 2560) ∧
    -Real.log (1581 / 2560) ≤ (481949701 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 4141)) (n := 12)
    (lo := (4819497 / 10000000)) (hi := (481949701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1581) = 1/(1581 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-481949701 / 1000000000) (-4819497 / 10000000) (Real.log (1581 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240723317 / 1000000000) ≤ -Real.log (1000000 / 1272169) ∧
    -Real.log (1000000 / 1272169) ≤ (120361659 / 500000000) := by
  have h := checkLog_sound (w := (272169 / 2272169)) (n := 12)
    (lo := (240723317 / 1000000000)) (hi := (120361659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272169 / 1000000) = 1/(1000000 / 1272169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240723317 / 1000000000) (120361659 / 500000000) (Real.log (1272169 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1272169 / 1000000) = -Real.log (1000000 / 1272169) := by
    rw [show ((1272169 / 1000000) : ℝ) = ((1000000 / 1272169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (99277 / 312500) ≤ -Real.log (727831 / 1000000) ∧
    -Real.log (727831 / 1000000) ≤ (317686401 / 1000000000) := by
  have h := checkLog_sound (w := (272169 / 1727831)) (n := 12)
    (lo := (99277 / 312500)) (hi := (317686401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727831) = 1/(727831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317686401 / 1000000000) (-99277 / 312500) (Real.log (727831 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48211153 / 200000000) ≤ -Real.log (62500 / 79537) ∧
    -Real.log (62500 / 79537) ≤ (120527883 / 500000000) := by
  have h := checkLog_sound (w := (17037 / 142037)) (n := 12)
    (lo := (48211153 / 200000000)) (hi := (120527883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79537 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79537 / 62500) = 1/(62500 / 79537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48211153 / 200000000) (120527883 / 500000000) (Real.log (79537 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (79537 / 62500) = -Real.log (62500 / 79537) := by
    rw [show ((79537 / 62500) : ℝ) = ((62500 / 79537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (79566937 / 250000000) ≤ -Real.log (45463 / 62500) ∧
    -Real.log (45463 / 62500) ≤ (318267749 / 1000000000) := by
  have h := checkLog_sound (w := (17037 / 107963)) (n := 12)
    (lo := (79566937 / 250000000)) (hi := (318267749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45463) = 1/(45463 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-318267749 / 1000000000) (-79566937 / 250000000) (Real.log (45463 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8969321 / 50000000) ≤ -Real.log (1000000 / 1196483) ∧
    -Real.log (1000000 / 1196483) ≤ (179386421 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 2196483)) (n := 12)
    (lo := (8969321 / 50000000)) (hi := (179386421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196483 / 1000000) = 1/(1000000 / 1196483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8969321 / 50000000) (179386421 / 1000000000) (Real.log (1196483 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1196483 / 1000000) = -Real.log (1000000 / 1196483) := by
    rw [show ((1196483 / 1000000) : ℝ) = ((1000000 / 1196483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27344617 / 125000000) ≤ -Real.log (803517 / 1000000) ∧
    -Real.log (803517 / 1000000) ≤ (218756937 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 1803517)) (n := 12)
    (lo := (27344617 / 125000000)) (hi := (218756937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803517) = 1/(803517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218756937 / 1000000000) (-27344617 / 125000000) (Real.log (803517 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (179652999 / 1000000000) ≤ -Real.log (500000 / 598401) ∧
    -Real.log (500000 / 598401) ≤ (179653 / 1000000) := by
  have h := checkLog_sound (w := (98401 / 1098401)) (n := 12)
    (lo := (179652999 / 1000000000)) (hi := (179653 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598401 / 500000) = 1/(500000 / 598401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (179652999 / 1000000000) (179653 / 1000000) (Real.log (598401 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (598401 / 500000) = -Real.log (500000 / 598401) := by
    rw [show ((598401 / 500000) : ℝ) = ((500000 / 598401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10957701 / 50000000) ≤ -Real.log (401599 / 500000) ∧
    -Real.log (401599 / 500000) ≤ (219154021 / 1000000000) := by
  have h := checkLog_sound (w := (98401 / 901599)) (n := 12)
    (lo := (10957701 / 50000000)) (hi := (219154021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401599) = 1/(401599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219154021 / 1000000000) (-10957701 / 50000000) (Real.log (401599 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (402893321 / 500000000) ≤ -Real.log (100000000000 / 223845667299) ∧
    -Real.log (100000000000 / 223845667299) ≤ (201446661 / 250000000) := by
  have h := checkLog_sound (w := (23845667299 / 423845667299)) (n := 12)
    (lo := (56319731 / 500000000)) (hi := (112639463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223845667299 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(223845667299 / 200000000000) = 1/(100000000000 / 223845667299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (402893321 / 500000000) (201446661 / 250000000) (Real.log (223845667299 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (223845667299 / 100000000000) = -Real.log (100000000000 / 223845667299) := by
    rw [show ((223845667299 / 100000000000) : ℝ) = ((100000000000 / 223845667299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (403579809 / 500000000) ≤ -Real.log (500000000000 / 1120766065211) ∧
    -Real.log (500000000000 / 1120766065211) ≤ (40357981 / 50000000) := by
  have h := checkLog_sound (w := (120766065211 / 2120766065211)) (n := 12)
    (lo := (57006219 / 500000000)) (hi := (114012439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120766065211 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120766065211 / 1000000000000) = 1/(500000000000 / 1120766065211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (403579809 / 500000000) (40357981 / 50000000) (Real.log (1120766065211 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1120766065211 / 500000000000) = -Real.log (500000000000 / 1120766065211) := by
    rw [show ((1120766065211 / 500000000000) : ℝ) = ((500000000000 / 1120766065211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (279204859 / 500000000) ≤ -Real.log (500000000000 / 873945325219) ∧
    -Real.log (500000000000 / 873945325219) ≤ (558409719 / 1000000000) := by
  have h := checkLog_sound (w := (373945325219 / 1373945325219)) (n := 12)
    (lo := (279204859 / 500000000)) (hi := (558409719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873945325219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873945325219 / 500000000000) = 1/(500000000000 / 873945325219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (279204859 / 500000000) (558409719 / 1000000000) (Real.log (873945325219 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (873945325219 / 500000000000) = -Real.log (500000000000 / 873945325219) := by
    rw [show ((873945325219 / 500000000000) : ℝ) = ((500000000000 / 873945325219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (559323513 / 1000000000) ≤ -Real.log (500000000000 / 874744297561) ∧
    -Real.log (500000000000 / 874744297561) ≤ (279661757 / 500000000) := by
  have h := checkLog_sound (w := (374744297561 / 1374744297561)) (n := 12)
    (lo := (559323513 / 1000000000)) (hi := (279661757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874744297561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874744297561 / 500000000000) = 1/(500000000000 / 874744297561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (559323513 / 1000000000) (279661757 / 500000000) (Real.log (874744297561 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (874744297561 / 500000000000) = -Real.log (500000000000 / 874744297561) := by
    rw [show ((874744297561 / 500000000000) : ℝ) = ((500000000000 / 874744297561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (99535839 / 250000000) ≤ -Real.log (125000000000 / 186132185131) ∧
    -Real.log (125000000000 / 186132185131) ≤ (398143357 / 1000000000) := by
  have h := checkLog_sound (w := (61132185131 / 311132185131)) (n := 12)
    (lo := (99535839 / 250000000)) (hi := (398143357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186132185131 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186132185131 / 125000000000) = 1/(125000000000 / 186132185131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (99535839 / 250000000) (398143357 / 1000000000) (Real.log (186132185131 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (186132185131 / 125000000000) = -Real.log (125000000000 / 186132185131) := by
    rw [show ((186132185131 / 125000000000) : ℝ) = ((125000000000 / 186132185131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (398807019 / 1000000000) ≤ -Real.log (125000000000 / 186255755119) ∧
    -Real.log (125000000000 / 186255755119) ≤ (19940351 / 50000000) := by
  have h := checkLog_sound (w := (61255755119 / 311255755119)) (n := 12)
    (lo := (398807019 / 1000000000)) (hi := (19940351 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186255755119 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186255755119 / 125000000000) = 1/(125000000000 / 186255755119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (398807019 / 1000000000) (19940351 / 50000000) (Real.log (186255755119 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (186255755119 / 125000000000) = -Real.log (125000000000 / 186255755119) := by
    rw [show ((186255755119 / 125000000000) : ℝ) = ((125000000000 / 186255755119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1975051 / 50000000) ≤ -Real.log (240317243199 / 250000000000) ∧
    -Real.log (240317243199 / 250000000000) ≤ (39501021 / 1000000000) := by
  have h := checkLog_sound (w := (9682756801 / 490317243199)) (n := 12)
    (lo := (1975051 / 50000000)) (hi := (39501021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240317243199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240317243199) = 1/(240317243199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-39501021 / 1000000000) (-1975051 / 50000000) (Real.log (240317243199 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9842629 / 250000000) ≤ -Real.log (961394430711 / 1000000000000) ∧
    -Real.log (961394430711 / 1000000000000) ≤ (39370517 / 1000000000) := by
  have h := checkLog_sound (w := (38605569289 / 1961394430711)) (n := 12)
    (lo := (9842629 / 250000000)) (hi := (39370517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961394430711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961394430711) = 1/(961394430711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-39370517 / 1000000000) (-9842629 / 250000000) (Real.log (961394430711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell226

end


