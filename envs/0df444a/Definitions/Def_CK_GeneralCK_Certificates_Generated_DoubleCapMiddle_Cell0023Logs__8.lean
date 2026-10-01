-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0023Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0023Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:04:44.565647+00:00
-- url     : https://prove2.me/theorems/a2dfbe95-fcd8-4c87-ae66-f44e382419d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0023Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0024Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0023Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0025Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0026Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0030Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0023Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0025Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0026Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0030Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0023Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0024Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0025Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0026Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0027Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0028Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0029Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0030Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0023Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0024Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0025Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0026Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0027Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0028Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0029Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0030Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0023Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0023
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

theorem reflection_log_1_neg : (198022943 / 500000000) ≤ -Real.log (640 / 951) ∧
    -Real.log (640 / 951) ≤ (396045887 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1591)) (n := 12)
    (lo := (198022943 / 500000000)) (hi := (396045887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 640) = 1/(640 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198022943 / 500000000) (396045887 / 1000000000) (Real.log (951 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (951 / 640) = -Real.log (640 / 951) := by
    rw [show ((951 / 640) : ℝ) = ((640 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26616417 / 40000000) ≤ -Real.log (329 / 640) ∧
    -Real.log (329 / 640) ≤ (332705213 / 500000000) := by
  have h := checkLog_sound (w := (311 / 969)) (n := 12)
    (lo := (26616417 / 40000000)) (hi := (332705213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 329) = 1/(329 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332705213 / 500000000) (-26616417 / 40000000) (Real.log (329 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (395256931 / 1000000000) ≤ -Real.log (2560 / 3801) ∧
    -Real.log (2560 / 3801) ≤ (98814233 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 6361)) (n := 12)
    (lo := (395256931 / 1000000000)) (hi := (98814233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3801 / 2560) = 1/(2560 / 3801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (395256931 / 1000000000) (98814233 / 250000000) (Real.log (3801 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3801 / 2560) = -Real.log (2560 / 3801) := by
    rw [show ((3801 / 2560) : ℝ) = ((2560 / 3801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82891673 / 125000000) ≤ -Real.log (1319 / 2560) ∧
    -Real.log (1319 / 2560) ≤ (132626677 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3879)) (n := 12)
    (lo := (82891673 / 125000000)) (hi := (132626677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1319) = 1/(1319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-132626677 / 200000000) (-82891673 / 125000000) (Real.log (1319 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (339492433 / 500000000) ≤ -Real.log (320 / 631) ∧
    -Real.log (320 / 631) ≤ (678984867 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 951)) (n := 12)
    (lo := (339492433 / 500000000)) (hi := (678984867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 320) = 1/(320 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (339492433 / 500000000) (678984867 / 1000000000) (Real.log (631 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (631 / 320) = -Real.log (320 / 631) := by
    rw [show ((631 / 320) : ℝ) = ((320 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (714219283 / 200000000) ≤ -Real.log (9 / 320) ∧
    -Real.log (9 / 320) ≤ (3571096421 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10 / 9) = 1/(9 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3571096421 / 1000000000) (-714219283 / 200000000) (Real.log (9 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67779557 / 100000000) ≤ -Real.log (1280 / 2521) ∧
    -Real.log (1280 / 2521) ≤ (677795571 / 1000000000) := by
  have h := checkLog_sound (w := (1241 / 3801)) (n := 12)
    (lo := (67779557 / 100000000)) (hi := (677795571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 1280) = 1/(1280 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67779557 / 100000000) (677795571 / 1000000000) (Real.log (2521 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2521 / 1280) = -Real.log (1280 / 2521) := by
    rw [show ((2521 / 1280) : ℝ) = ((1280 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3491053707 / 1000000000) ≤ -Real.log (39 / 1280) ∧
    -Real.log (39 / 1280) ≤ (3491053713 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 39) = 1/(39 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3491053713 / 1000000000) (-3491053707 / 1000000000) (Real.log (39 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (554116121 / 1000000000) ≤ -Real.log (500000 / 870201) ∧
    -Real.log (500000 / 870201) ≤ (277058061 / 500000000) := by
  have h := checkLog_sound (w := (370201 / 1370201)) (n := 12)
    (lo := (554116121 / 1000000000)) (hi := (277058061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870201 / 500000) = 1/(500000 / 870201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (554116121 / 1000000000) (277058061 / 500000000) (Real.log (870201 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (870201 / 500000) = -Real.log (500000 / 870201) := by
    rw [show ((870201 / 500000) : ℝ) = ((500000 / 870201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1348620997 / 1000000000) ≤ -Real.log (129799 / 500000) ∧
    -Real.log (129799 / 500000) ≤ (1348620999 / 1000000000) := by
  have h := checkLog_sound (w := (120201 / 379799)) (n := 12)
    (lo := (655473817 / 1000000000)) (hi := (327736909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 129799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 129799) = 1/(129799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1348620999 / 1000000000) (-1348620997 / 1000000000) (Real.log (129799 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138900077 / 250000000) ≤ -Real.log (1000000 / 1742987) ∧
    -Real.log (1000000 / 1742987) ≤ (555600309 / 1000000000) := by
  have h := checkLog_sound (w := (742987 / 2742987)) (n := 12)
    (lo := (138900077 / 250000000)) (hi := (555600309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1742987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1742987 / 1000000) = 1/(1000000 / 1742987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138900077 / 250000000) (555600309 / 1000000000) (Real.log (1742987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1742987 / 1000000) = -Real.log (1000000 / 1742987) := by
    rw [show ((1742987 / 1000000) : ℝ) = ((1000000 / 1742987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1358628611 / 1000000000) ≤ -Real.log (257013 / 1000000) ∧
    -Real.log (257013 / 1000000) ≤ (1358628613 / 1000000000) := by
  have h := checkLog_sound (w := (242987 / 757013)) (n := 12)
    (lo := (665481431 / 1000000000)) (hi := (83185179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 257013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 257013) = 1/(257013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1358628613 / 1000000000) (-1358628611 / 1000000000) (Real.log (257013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (479384491 / 1000000000) ≤ -Real.log (25000 / 40377) ∧
    -Real.log (25000 / 40377) ≤ (119846123 / 250000000) := by
  have h := checkLog_sound (w := (15377 / 65377)) (n := 12)
    (lo := (479384491 / 1000000000)) (hi := (119846123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40377 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40377 / 25000) = 1/(25000 / 40377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (479384491 / 1000000000) (119846123 / 250000000) (Real.log (40377 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (40377 / 25000) = -Real.log (25000 / 40377) := by
    rw [show ((40377 / 25000) : ℝ) = ((25000 / 40377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (954719757 / 1000000000) ≤ -Real.log (9623 / 25000) ∧
    -Real.log (9623 / 25000) ≤ (954719759 / 1000000000) := by
  have h := checkLog_sound (w := (2877 / 22123)) (n := 12)
    (lo := (261572577 / 1000000000)) (hi := (130786289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9623) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9623) = 1/(9623 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-954719759 / 1000000000) (-954719757 / 1000000000) (Real.log (9623 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (15035919 / 31250000) ≤ -Real.log (1000000 / 1617933) ∧
    -Real.log (1000000 / 1617933) ≤ (481149409 / 1000000000) := by
  have h := checkLog_sound (w := (617933 / 2617933)) (n := 12)
    (lo := (15035919 / 31250000)) (hi := (481149409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617933 / 1000000) = 1/(1000000 / 1617933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15035919 / 31250000) (481149409 / 1000000000) (Real.log (1617933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1617933 / 1000000) = -Real.log (1000000 / 1617933) := by
    rw [show ((1617933 / 1000000) : ℝ) = ((1000000 / 1617933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (240539823 / 250000000) ≤ -Real.log (382067 / 1000000) ∧
    -Real.log (382067 / 1000000) ≤ (481079647 / 500000000) := by
  have h := checkLog_sound (w := (117933 / 882067)) (n := 12)
    (lo := (16813257 / 62500000)) (hi := (269012113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 382067) = 1/(382067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-481079647 / 500000000) (-240539823 / 250000000) (Real.log (382067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (951368559 / 500000000) ≤ -Real.log (500000000000 / 3352109800537) ∧
    -Real.log (500000000000 / 3352109800537) ≤ (1902737121 / 1000000000) := by
  have h := checkLog_sound (w := (1352109800537 / 5352109800537)) (n := 12)
    (lo := (258221379 / 500000000)) (hi := (516442759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3352109800537 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3352109800537 / 2000000000000) = 1/(500000000000 / 3352109800537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (951368559 / 500000000) (1902737121 / 1000000000) (Real.log (3352109800537 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3352109800537 / 500000000000) = -Real.log (500000000000 / 3352109800537) := by
    rw [show ((3352109800537 / 500000000000) : ℝ) = ((500000000000 / 3352109800537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (957114459 / 500000000) ≤ -Real.log (500000000000 / 3390853770043) ∧
    -Real.log (500000000000 / 3390853770043) ≤ (1914228921 / 1000000000) := by
  have h := checkLog_sound (w := (1390853770043 / 5390853770043)) (n := 12)
    (lo := (263967279 / 500000000)) (hi := (527934559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3390853770043 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3390853770043 / 2000000000000) = 1/(500000000000 / 3390853770043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (957114459 / 500000000) (1914228921 / 1000000000) (Real.log (3390853770043 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3390853770043 / 500000000000) = -Real.log (500000000000 / 3390853770043) := by
    rw [show ((3390853770043 / 500000000000) : ℝ) = ((500000000000 / 3390853770043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (179263031 / 125000000) ≤ -Real.log (100000000000 / 419588485919) ∧
    -Real.log (100000000000 / 419588485919) ≤ (1434104251 / 1000000000) := by
  have h := checkLog_sound (w := (19588485919 / 819588485919)) (n := 12)
    (lo := (1494059 / 31250000)) (hi := (47809889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419588485919 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(419588485919 / 400000000000) = 1/(100000000000 / 419588485919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (179263031 / 125000000) (1434104251 / 1000000000) (Real.log (419588485919 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (419588485919 / 100000000000) = -Real.log (100000000000 / 419588485919) := by
    rw [show ((419588485919 / 100000000000) : ℝ) = ((100000000000 / 419588485919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14433087 / 10000000) ≤ -Real.log (250000000000 / 1058670992261) ∧
    -Real.log (250000000000 / 1058670992261) ≤ (1443308703 / 1000000000) := by
  have h := checkLog_sound (w := (58670992261 / 2058670992261)) (n := 12)
    (lo := (2850717 / 50000000)) (hi := (57014341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1058670992261 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1058670992261 / 1000000000000) = 1/(250000000000 / 1058670992261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14433087 / 10000000) (1443308703 / 1000000000) (Real.log (1058670992261 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1058670992261 / 250000000000) = -Real.log (250000000000 / 1058670992261) := by
    rw [show ((1058670992261 / 250000000000) : ℝ) = ((250000000000 / 1058670992261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0023

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0024Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0024
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

theorem reflection_log_1_neg : (395256931 / 1000000000) ≤ -Real.log (2560 / 3801) ∧
    -Real.log (2560 / 3801) ≤ (98814233 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 6361)) (n := 12)
    (lo := (395256931 / 1000000000)) (hi := (98814233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3801 / 2560) = 1/(2560 / 3801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (395256931 / 1000000000) (98814233 / 250000000) (Real.log (3801 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3801 / 2560) = -Real.log (2560 / 3801) := by
    rw [show ((3801 / 2560) : ℝ) = ((2560 / 3801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82891673 / 125000000) ≤ -Real.log (1319 / 2560) ∧
    -Real.log (1319 / 2560) ≤ (132626677 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3879)) (n := 12)
    (lo := (82891673 / 125000000)) (hi := (132626677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1319) = 1/(1319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-132626677 / 200000000) (-82891673 / 125000000) (Real.log (1319 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (394467353 / 1000000000) ≤ -Real.log (1280 / 1899) ∧
    -Real.log (1280 / 1899) ≤ (197233677 / 500000000) := by
  have h := checkLog_sound (w := (619 / 3179)) (n := 12)
    (lo := (394467353 / 1000000000)) (hi := (197233677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1280) = 1/(1280 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (394467353 / 1000000000) (197233677 / 500000000) (Real.log (1899 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1899 / 1280) = -Real.log (1280 / 1899) := by
    rw [show ((1899 / 1280) : ℝ) = ((1280 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (660861517 / 1000000000) ≤ -Real.log (661 / 1280) ∧
    -Real.log (661 / 1280) ≤ (330430759 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1941)) (n := 12)
    (lo := (660861517 / 1000000000)) (hi := (330430759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 661) = 1/(661 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330430759 / 500000000) (-660861517 / 1000000000) (Real.log (661 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67779557 / 100000000) ≤ -Real.log (1280 / 2521) ∧
    -Real.log (1280 / 2521) ≤ (677795571 / 1000000000) := by
  have h := checkLog_sound (w := (1241 / 3801)) (n := 12)
    (lo := (67779557 / 100000000)) (hi := (677795571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 1280) = 1/(1280 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (67779557 / 100000000) (677795571 / 1000000000) (Real.log (2521 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2521 / 1280) = -Real.log (1280 / 2521) := by
    rw [show ((2521 / 1280) : ℝ) = ((1280 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3491053707 / 1000000000) ≤ -Real.log (39 / 1280) ∧
    -Real.log (39 / 1280) ≤ (3491053713 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 39) = 1/(39 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3491053713 / 1000000000) (-3491053707 / 1000000000) (Real.log (39 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (676604857 / 1000000000) ≤ -Real.log (640 / 1259) ∧
    -Real.log (640 / 1259) ≤ (338302429 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1899)) (n := 12)
    (lo := (676604857 / 1000000000)) (hi := (338302429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 640) = 1/(640 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (676604857 / 1000000000) (338302429 / 500000000) (Real.log (1259 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1259 / 640) = -Real.log (640 / 1259) := by
    rw [show ((1259 / 640) : ℝ) = ((640 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (427118217 / 125000000) ≤ -Real.log (21 / 640) ∧
    -Real.log (21 / 640) ≤ (3416945741 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 21) = 1/(21 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3416945741 / 1000000000) (-427118217 / 125000000) (Real.log (21 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (552648717 / 1000000000) ≤ -Real.log (20000 / 34757) ∧
    -Real.log (20000 / 34757) ≤ (276324359 / 500000000) := by
  have h := checkLog_sound (w := (14757 / 54757)) (n := 12)
    (lo := (552648717 / 1000000000)) (hi := (276324359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34757 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34757 / 20000) = 1/(20000 / 34757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (552648717 / 1000000000) (276324359 / 500000000) (Real.log (34757 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (34757 / 20000) = -Real.log (20000 / 34757) := by
    rw [show ((34757 / 20000) : ℝ) = ((20000 / 34757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1338838419 / 1000000000) ≤ -Real.log (5243 / 20000) ∧
    -Real.log (5243 / 20000) ≤ (1338838421 / 1000000000) := by
  have h := checkLog_sound (w := (4757 / 15243)) (n := 12)
    (lo := (645691239 / 1000000000)) (hi := (16142281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 5243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10000 / 5243) = 1/(5243 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1338838421 / 1000000000) (-1338838419 / 1000000000) (Real.log (5243 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (110823339 / 200000000) ≤ -Real.log (1000000 / 1740403) ∧
    -Real.log (1000000 / 1740403) ≤ (69264587 / 125000000) := by
  have h := checkLog_sound (w := (740403 / 2740403)) (n := 12)
    (lo := (110823339 / 200000000)) (hi := (69264587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1740403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1740403 / 1000000) = 1/(1000000 / 1740403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (110823339 / 200000000) (69264587 / 125000000) (Real.log (1740403 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1740403 / 1000000) = -Real.log (1000000 / 1740403) := by
    rw [show ((1740403 / 1000000) : ℝ) = ((1000000 / 1740403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1348624849 / 1000000000) ≤ -Real.log (259597 / 1000000) ∧
    -Real.log (259597 / 1000000) ≤ (1348624851 / 1000000000) := by
  have h := checkLog_sound (w := (240403 / 759597)) (n := 12)
    (lo := (655477669 / 1000000000)) (hi := (65547767 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 259597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 259597) = 1/(259597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1348624851 / 1000000000) (-1348624849 / 1000000000) (Real.log (259597 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (477643123 / 1000000000) ≤ -Real.log (100000 / 161227) ∧
    -Real.log (100000 / 161227) ≤ (119410781 / 250000000) := by
  have h := checkLog_sound (w := (61227 / 261227)) (n := 12)
    (lo := (477643123 / 1000000000)) (hi := (119410781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161227 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161227 / 100000) = 1/(100000 / 161227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (477643123 / 1000000000) (119410781 / 250000000) (Real.log (161227 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161227 / 100000) = -Real.log (100000 / 161227) := by
    rw [show ((161227 / 100000) : ℝ) = ((100000 / 161227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (947446057 / 1000000000) ≤ -Real.log (38773 / 100000) ∧
    -Real.log (38773 / 100000) ≤ (947446059 / 1000000000) := by
  have h := checkLog_sound (w := (11227 / 88773)) (n := 12)
    (lo := (254298877 / 1000000000)) (hi := (127149439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38773) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38773) = 1/(38773 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-947446059 / 1000000000) (-947446057 / 1000000000) (Real.log (38773 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47938511 / 100000000) ≤ -Real.log (1000000 / 1615081) ∧
    -Real.log (1000000 / 1615081) ≤ (479385111 / 1000000000) := by
  have h := checkLog_sound (w := (615081 / 2615081)) (n := 12)
    (lo := (47938511 / 100000000)) (hi := (479385111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615081 / 1000000) = 1/(1000000 / 1615081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47938511 / 100000000) (479385111 / 1000000000) (Real.log (1615081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1615081 / 1000000) = -Real.log (1000000 / 1615081) := by
    rw [show ((1615081 / 1000000) : ℝ) = ((1000000 / 1615081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (190944471 / 200000000) ≤ -Real.log (384919 / 1000000) ∧
    -Real.log (384919 / 1000000) ≤ (954722357 / 1000000000) := by
  have h := checkLog_sound (w := (115081 / 884919)) (n := 12)
    (lo := (10463007 / 40000000)) (hi := (32696897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384919) = 1/(384919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-954722357 / 1000000000) (-190944471 / 200000000) (Real.log (384919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (378297427 / 200000000) ≤ -Real.log (500000000000 / 3314609956131) ∧
    -Real.log (500000000000 / 3314609956131) ≤ (945743569 / 500000000) := by
  have h := checkLog_sound (w := (1314609956131 / 5314609956131)) (n := 12)
    (lo := (20207711 / 40000000)) (hi := (63149097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3314609956131 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3314609956131 / 2000000000000) = 1/(500000000000 / 3314609956131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (378297427 / 200000000) (945743569 / 500000000) (Real.log (3314609956131 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3314609956131 / 500000000000) = -Real.log (500000000000 / 3314609956131) := by
    rw [show ((3314609956131 / 500000000000) : ℝ) = ((500000000000 / 3314609956131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (237842693 / 125000000) ≤ -Real.log (100000000000 / 670424927869) ∧
    -Real.log (100000000000 / 670424927869) ≤ (1902741547 / 1000000000) := by
  have h := checkLog_sound (w := (270424927869 / 1070424927869)) (n := 12)
    (lo := (32277949 / 62500000)) (hi := (103289437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670424927869 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(670424927869 / 400000000000) = 1/(100000000000 / 670424927869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (237842693 / 125000000) (1902741547 / 1000000000) (Real.log (670424927869 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670424927869 / 100000000000) = -Real.log (100000000000 / 670424927869) := by
    rw [show ((670424927869 / 100000000000) : ℝ) = ((100000000000 / 670424927869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (71254459 / 50000000) ≤ -Real.log (250000000000 / 1039557166069) ∧
    -Real.log (250000000000 / 1039557166069) ≤ (1425089183 / 1000000000) := by
  have h := checkLog_sound (w := (39557166069 / 2039557166069)) (n := 12)
    (lo := (1939741 / 50000000)) (hi := (38794821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1039557166069 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1039557166069 / 1000000000000) = 1/(250000000000 / 1039557166069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (71254459 / 50000000) (1425089183 / 1000000000) (Real.log (1039557166069 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1039557166069 / 250000000000) = -Real.log (250000000000 / 1039557166069) := by
    rw [show ((1039557166069 / 250000000000) : ℝ) = ((250000000000 / 1039557166069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (286821493 / 200000000) ≤ -Real.log (500000000000 / 2097949178919) ∧
    -Real.log (500000000000 / 2097949178919) ≤ (358526867 / 250000000) := by
  have h := checkLog_sound (w := (97949178919 / 4097949178919)) (n := 12)
    (lo := (9562621 / 200000000)) (hi := (23906553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2097949178919 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2097949178919 / 2000000000000) = 1/(500000000000 / 2097949178919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (286821493 / 200000000) (358526867 / 250000000) (Real.log (2097949178919 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2097949178919 / 500000000000) = -Real.log (500000000000 / 2097949178919) := by
    rw [show ((2097949178919 / 500000000000) : ℝ) = ((500000000000 / 2097949178919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0024

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0025Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0025
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

theorem reflection_log_1_neg : (394467353 / 1000000000) ≤ -Real.log (1280 / 1899) ∧
    -Real.log (1280 / 1899) ≤ (197233677 / 500000000) := by
  have h := checkLog_sound (w := (619 / 3179)) (n := 12)
    (lo := (394467353 / 1000000000)) (hi := (197233677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1280) = 1/(1280 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (394467353 / 1000000000) (197233677 / 500000000) (Real.log (1899 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1899 / 1280) = -Real.log (1280 / 1899) := by
    rw [show ((1899 / 1280) : ℝ) = ((1280 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (660861517 / 1000000000) ≤ -Real.log (661 / 1280) ∧
    -Real.log (661 / 1280) ≤ (330430759 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1941)) (n := 12)
    (lo := (660861517 / 1000000000)) (hi := (330430759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 661) = 1/(661 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-330430759 / 500000000) (-660861517 / 1000000000) (Real.log (661 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12302411 / 31250000) ≤ -Real.log (512 / 759) ∧
    -Real.log (512 / 759) ≤ (393677153 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1271)) (n := 12)
    (lo := (12302411 / 31250000)) (hi := (393677153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 512) = 1/(512 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12302411 / 31250000) (393677153 / 1000000000) (Real.log (759 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (759 / 512) = -Real.log (512 / 759) := by
    rw [show ((759 / 512) : ℝ) = ((512 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (658594799 / 1000000000) ≤ -Real.log (265 / 512) ∧
    -Real.log (265 / 512) ≤ (1646487 / 2500000) := by
  have h := checkLog_sound (w := (247 / 777)) (n := 12)
    (lo := (658594799 / 1000000000)) (hi := (1646487 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 265) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 265) = 1/(265 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1646487 / 2500000) (-658594799 / 1000000000) (Real.log (265 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (676604857 / 1000000000) ≤ -Real.log (640 / 1259) ∧
    -Real.log (640 / 1259) ≤ (338302429 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1899)) (n := 12)
    (lo := (676604857 / 1000000000)) (hi := (338302429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 640) = 1/(640 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (676604857 / 1000000000) (338302429 / 500000000) (Real.log (1259 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259 / 640) = -Real.log (640 / 1259) := by
    rw [show ((1259 / 640) : ℝ) = ((640 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (427118217 / 125000000) ≤ -Real.log (21 / 640) ∧
    -Real.log (21 / 640) ≤ (3416945741 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 21) = 1/(21 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3416945741 / 1000000000) (-427118217 / 125000000) (Real.log (21 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (27016509 / 40000000) ≤ -Real.log (256 / 503) ∧
    -Real.log (256 / 503) ≤ (337706363 / 500000000) := by
  have h := checkLog_sound (w := (247 / 759)) (n := 12)
    (lo := (27016509 / 40000000)) (hi := (337706363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 256) = 1/(256 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (27016509 / 40000000) (337706363 / 500000000) (Real.log (503 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (503 / 256) = -Real.log (256 / 503) := by
    rw [show ((503 / 256) : ℝ) = ((256 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104623527 / 31250000) ≤ -Real.log (9 / 256) ∧
    -Real.log (9 / 256) ≤ (3347952869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 9) = 1/(9 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3347952869 / 1000000000) (-104623527 / 31250000) (Real.log (9 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137799111 / 250000000) ≤ -Real.log (31250 / 54229) ∧
    -Real.log (31250 / 54229) ≤ (110239289 / 200000000) := by
  have h := checkLog_sound (w := (22979 / 85479)) (n := 12)
    (lo := (137799111 / 250000000)) (hi := (110239289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54229 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54229 / 31250) = 1/(31250 / 54229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137799111 / 250000000) (110239289 / 200000000) (Real.log (54229 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54229 / 31250) = -Real.log (31250 / 54229) := by
    rw [show ((54229 / 31250) : ℝ) = ((31250 / 54229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (664631977 / 500000000) ≤ -Real.log (8271 / 31250) ∧
    -Real.log (8271 / 31250) ≤ (332315989 / 250000000) := by
  have h := checkLog_sound (w := (3677 / 11948)) (n := 12)
    (lo := (318058387 / 500000000)) (hi := (25444671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8271) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 8271) = 1/(8271 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-332315989 / 250000000) (-664631977 / 500000000) (Real.log (8271 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138162323 / 250000000) ≤ -Real.log (1000000 / 1737851) ∧
    -Real.log (1000000 / 1737851) ≤ (552649293 / 1000000000) := by
  have h := checkLog_sound (w := (737851 / 2737851)) (n := 12)
    (lo := (138162323 / 250000000)) (hi := (552649293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737851 / 1000000) = 1/(1000000 / 1737851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138162323 / 250000000) (552649293 / 1000000000) (Real.log (1737851 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1737851 / 1000000) = -Real.log (1000000 / 1737851) := by
    rw [show ((1737851 / 1000000) : ℝ) = ((1000000 / 1737851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (669421117 / 500000000) ≤ -Real.log (262149 / 1000000) ∧
    -Real.log (262149 / 1000000) ≤ (334710559 / 250000000) := by
  have h := checkLog_sound (w := (237851 / 762149)) (n := 12)
    (lo := (322847527 / 500000000)) (hi := (129139011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 262149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 262149) = 1/(262149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-334710559 / 250000000) (-669421117 / 500000000) (Real.log (262149 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (475923571 / 1000000000) ≤ -Real.log (2000 / 3219) ∧
    -Real.log (2000 / 3219) ≤ (118980893 / 250000000) := by
  have h := checkLog_sound (w := (1219 / 5219)) (n := 12)
    (lo := (475923571 / 1000000000)) (hi := (118980893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2000) = 1/(2000 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (475923571 / 1000000000) (118980893 / 250000000) (Real.log (3219 / 2000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3219 / 2000) = -Real.log (2000 / 3219) := by
    rw [show ((3219 / 2000) : ℝ) = ((2000 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (940327309 / 1000000000) ≤ -Real.log (781 / 2000) ∧
    -Real.log (781 / 2000) ≤ (940327311 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1781)) (n := 12)
    (lo := (247180129 / 1000000000)) (hi := (24718013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000 / 781) = 1/(781 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-940327311 / 1000000000) (-940327309 / 1000000000) (Real.log (781 / 2000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14926367 / 31250000) ≤ -Real.log (1000000 / 1612271) ∧
    -Real.log (1000000 / 1612271) ≤ (95528749 / 200000000) := by
  have h := checkLog_sound (w := (612271 / 2612271)) (n := 12)
    (lo := (14926367 / 31250000)) (hi := (95528749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1612271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1612271 / 1000000) = 1/(1000000 / 1612271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14926367 / 31250000) (95528749 / 200000000) (Real.log (1612271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1612271 / 1000000) = -Real.log (1000000 / 1612271) := by
    rw [show ((1612271 / 1000000) : ℝ) = ((1000000 / 1612271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236862159 / 250000000) ≤ -Real.log (387729 / 1000000) ∧
    -Real.log (387729 / 1000000) ≤ (473724319 / 500000000) := by
  have h := checkLog_sound (w := (112271 / 887729)) (n := 12)
    (lo := (15893841 / 62500000)) (hi := (254301457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 387729) = 1/(387729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-473724319 / 500000000) (-236862159 / 250000000) (Real.log (387729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (940230199 / 500000000) ≤ -Real.log (125000000000 / 819565348809) ∧
    -Real.log (125000000000 / 819565348809) ≤ (1880460401 / 1000000000) := by
  have h := checkLog_sound (w := (319565348809 / 1319565348809)) (n := 12)
    (lo := (247083019 / 500000000)) (hi := (494166039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819565348809 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(819565348809 / 500000000000) = 1/(125000000000 / 819565348809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (940230199 / 500000000) (1880460401 / 1000000000) (Real.log (819565348809 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (819565348809 / 125000000000) = -Real.log (125000000000 / 819565348809) := by
    rw [show ((819565348809 / 125000000000) : ℝ) = ((125000000000 / 819565348809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (75659661 / 40000000) ≤ -Real.log (500000000000 / 3314624507437) ∧
    -Real.log (500000000000 / 3314624507437) ≤ (236436441 / 125000000) := by
  have h := checkLog_sound (w := (1314624507437 / 5314624507437)) (n := 12)
    (lo := (101039433 / 200000000)) (hi := (252598583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3314624507437 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3314624507437 / 2000000000000) = 1/(500000000000 / 3314624507437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (75659661 / 40000000) (236436441 / 125000000) (Real.log (3314624507437 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3314624507437 / 500000000000) = -Real.log (500000000000 / 3314624507437) := by
    rw [show ((3314624507437 / 500000000000) : ℝ) = ((500000000000 / 3314624507437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553223 / 390625) ≤ -Real.log (500000000000 / 2060819462227) ∧
    -Real.log (500000000000 / 2060819462227) ≤ (1416250883 / 1000000000) := by
  have h := checkLog_sound (w := (60819462227 / 4060819462227)) (n := 12)
    (lo := (748913 / 25000000)) (hi := (29956521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2060819462227 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2060819462227 / 2000000000000) = 1/(500000000000 / 2060819462227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553223 / 390625) (1416250883 / 1000000000) (Real.log (2060819462227 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2060819462227 / 500000000000) = -Real.log (500000000000 / 2060819462227) := by
    rw [show ((2060819462227 / 500000000000) : ℝ) = ((500000000000 / 2060819462227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1425092379 / 1000000000) ≤ -Real.log (500000000000 / 2079120983987) ∧
    -Real.log (500000000000 / 2079120983987) ≤ (712546191 / 500000000) := by
  have h := checkLog_sound (w := (79120983987 / 4079120983987)) (n := 12)
    (lo := (38798019 / 1000000000)) (hi := (1939901 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2079120983987 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2079120983987 / 2000000000000) = 1/(500000000000 / 2079120983987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1425092379 / 1000000000) (712546191 / 500000000) (Real.log (2079120983987 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2079120983987 / 500000000000) = -Real.log (500000000000 / 2079120983987) := by
    rw [show ((2079120983987 / 500000000000) : ℝ) = ((500000000000 / 2079120983987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0025

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0026Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0026
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

theorem reflection_log_1_neg : (12302411 / 31250000) ≤ -Real.log (512 / 759) ∧
    -Real.log (512 / 759) ≤ (393677153 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1271)) (n := 12)
    (lo := (12302411 / 31250000)) (hi := (393677153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 512) = 1/(512 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12302411 / 31250000) (393677153 / 1000000000) (Real.log (759 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (759 / 512) = -Real.log (512 / 759) := by
    rw [show ((759 / 512) : ℝ) = ((512 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (658594799 / 1000000000) ≤ -Real.log (265 / 512) ∧
    -Real.log (265 / 512) ≤ (1646487 / 2500000) := by
  have h := checkLog_sound (w := (247 / 777)) (n := 12)
    (lo := (658594799 / 1000000000)) (hi := (1646487 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 265) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 265) = 1/(265 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1646487 / 2500000) (-658594799 / 1000000000) (Real.log (265 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15715453 / 40000000) ≤ -Real.log (160 / 237) ∧
    -Real.log (160 / 237) ≤ (196443163 / 500000000) := by
  have h := checkLog_sound (w := (77 / 397)) (n := 12)
    (lo := (15715453 / 40000000)) (hi := (196443163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 160) = 1/(160 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15715453 / 40000000) (196443163 / 500000000) (Real.log (237 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (237 / 160) = -Real.log (160 / 237) := by
    rw [show ((237 / 160) : ℝ) = ((160 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (656333207 / 1000000000) ≤ -Real.log (83 / 160) ∧
    -Real.log (83 / 160) ≤ (82041651 / 125000000) := by
  have h := checkLog_sound (w := (77 / 243)) (n := 12)
    (lo := (656333207 / 1000000000)) (hi := (82041651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 83) = 1/(83 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-82041651 / 125000000) (-656333207 / 1000000000) (Real.log (83 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (27016509 / 40000000) ≤ -Real.log (256 / 503) ∧
    -Real.log (256 / 503) ≤ (337706363 / 500000000) := by
  have h := checkLog_sound (w := (247 / 759)) (n := 12)
    (lo := (27016509 / 40000000)) (hi := (337706363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 256) = 1/(256 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (27016509 / 40000000) (337706363 / 500000000) (Real.log (503 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (503 / 256) = -Real.log (256 / 503) := by
    rw [show ((503 / 256) : ℝ) = ((256 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104623527 / 31250000) ≤ -Real.log (9 / 256) ∧
    -Real.log (9 / 256) ≤ (3347952869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 9) = 1/(9 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3347952869 / 1000000000) (-104623527 / 31250000) (Real.log (9 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67421917 / 100000000) ≤ -Real.log (80 / 157) ∧
    -Real.log (80 / 157) ≤ (674219171 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 237)) (n := 12)
    (lo := (67421917 / 100000000)) (hi := (674219171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 80) = 1/(80 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67421917 / 100000000) (674219171 / 1000000000) (Real.log (157 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (157 / 80) = -Real.log (80 / 157) := by
    rw [show ((157 / 80) : ℝ) = ((80 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3283414343 / 1000000000) ≤ -Real.log (3 / 80) ∧
    -Real.log (3 / 80) ≤ (820853587 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 3) = 1/(3 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-820853587 / 250000000) (-3283414343 / 1000000000) (Real.log (3 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (109951759 / 200000000) ≤ -Real.log (200000 / 346567) ∧
    -Real.log (200000 / 346567) ≤ (137439699 / 250000000) := by
  have h := checkLog_sound (w := (146567 / 546567)) (n := 12)
    (lo := (109951759 / 200000000)) (hi := (137439699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346567 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346567 / 200000) = 1/(200000 / 346567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (109951759 / 200000000) (137439699 / 250000000) (Real.log (346567 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (346567 / 200000) = -Real.log (200000 / 346567) := by
    rw [show ((346567 / 200000) : ℝ) = ((200000 / 346567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1319888833 / 1000000000) ≤ -Real.log (53433 / 200000) ∧
    -Real.log (53433 / 200000) ≤ (263977767 / 200000000) := by
  have h := checkLog_sound (w := (46567 / 153433)) (n := 12)
    (lo := (626741653 / 1000000000)) (hi := (313370827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 53433) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 53433) = 1/(53433 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-263977767 / 200000000) (-1319888833 / 1000000000) (Real.log (53433 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (551197597 / 1000000000) ≤ -Real.log (100000 / 173533) ∧
    -Real.log (100000 / 173533) ≤ (275598799 / 500000000) := by
  have h := checkLog_sound (w := (73533 / 273533)) (n := 12)
    (lo := (551197597 / 1000000000)) (hi := (275598799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173533 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173533 / 100000) = 1/(100000 / 173533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (551197597 / 1000000000) (275598799 / 500000000) (Real.log (173533 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (173533 / 100000) = -Real.log (100000 / 173533) := by
    rw [show ((173533 / 100000) : ℝ) = ((100000 / 173533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1329271511 / 1000000000) ≤ -Real.log (26467 / 100000) ∧
    -Real.log (26467 / 100000) ≤ (1329271513 / 1000000000) := by
  have h := checkLog_sound (w := (23533 / 76467)) (n := 12)
    (lo := (636124331 / 1000000000)) (hi := (159031083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 26467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 26467) = 1/(26467 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1329271513 / 1000000000) (-1329271511 / 1000000000) (Real.log (26467 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (474223463 / 1000000000) ≤ -Real.log (500000 / 803383) ∧
    -Real.log (500000 / 803383) ≤ (59277933 / 125000000) := by
  have h := checkLog_sound (w := (303383 / 1303383)) (n := 12)
    (lo := (474223463 / 1000000000)) (hi := (59277933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803383 / 500000) = 1/(500000 / 803383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (474223463 / 1000000000) (59277933 / 125000000) (Real.log (803383 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (803383 / 500000) = -Real.log (500000 / 803383) := by
    rw [show ((803383 / 500000) : ℝ) = ((500000 / 803383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (933350423 / 1000000000) ≤ -Real.log (196617 / 500000) ∧
    -Real.log (196617 / 500000) ≤ (37334017 / 40000000) := by
  have h := checkLog_sound (w := (53383 / 446617)) (n := 12)
    (lo := (240203243 / 1000000000)) (hi := (60050811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 196617) = 1/(196617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-37334017 / 40000000) (-933350423 / 1000000000) (Real.log (196617 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (475924193 / 1000000000) ≤ -Real.log (1000000 / 1609501) ∧
    -Real.log (1000000 / 1609501) ≤ (237962097 / 500000000) := by
  have h := checkLog_sound (w := (609501 / 2609501)) (n := 12)
    (lo := (475924193 / 1000000000)) (hi := (237962097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609501 / 1000000) = 1/(1000000 / 1609501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (475924193 / 1000000000) (237962097 / 500000000) (Real.log (1609501 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1609501 / 1000000) = -Real.log (1000000 / 1609501) := by
    rw [show ((1609501 / 1000000) : ℝ) = ((1000000 / 1609501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (940329869 / 1000000000) ≤ -Real.log (390499 / 1000000) ∧
    -Real.log (390499 / 1000000) ≤ (940329871 / 1000000000) := by
  have h := checkLog_sound (w := (109501 / 890499)) (n := 12)
    (lo := (247182689 / 1000000000)) (hi := (24718269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 390499) = 1/(390499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-940329871 / 1000000000) (-940329869 / 1000000000) (Real.log (390499 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (467411907 / 250000000) ≤ -Real.log (250000000000 / 1621502629461) ∧
    -Real.log (250000000000 / 1621502629461) ≤ (1869647631 / 1000000000) := by
  have h := checkLog_sound (w := (621502629461 / 2621502629461)) (n := 12)
    (lo := (120838317 / 250000000)) (hi := (483353269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621502629461 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1621502629461 / 1000000000000) = 1/(250000000000 / 1621502629461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (467411907 / 250000000) (1869647631 / 1000000000) (Real.log (1621502629461 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1621502629461 / 250000000000) = -Real.log (250000000000 / 1621502629461) := by
    rw [show ((1621502629461 / 250000000000) : ℝ) = ((250000000000 / 1621502629461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1880469107 / 1000000000) ≤ -Real.log (500000000000 / 3278289945971) ∧
    -Real.log (500000000000 / 3278289945971) ≤ (188046911 / 100000000) := by
  have h := checkLog_sound (w := (1278289945971 / 5278289945971)) (n := 12)
    (lo := (494174747 / 1000000000)) (hi := (123543687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3278289945971 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3278289945971 / 2000000000000) = 1/(500000000000 / 3278289945971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1880469107 / 1000000000) (188046911 / 100000000) (Real.log (3278289945971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3278289945971 / 500000000000) = -Real.log (500000000000 / 3278289945971) := by
    rw [show ((3278289945971 / 500000000000) : ℝ) = ((500000000000 / 3278289945971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (703786943 / 500000000) ≤ -Real.log (500000000000 / 2043015100423) ∧
    -Real.log (500000000000 / 2043015100423) ≤ (1407573889 / 1000000000) := by
  have h := checkLog_sound (w := (43015100423 / 4043015100423)) (n := 12)
    (lo := (10639763 / 500000000)) (hi := (21279527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2043015100423 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2043015100423 / 2000000000000) = 1/(500000000000 / 2043015100423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (703786943 / 500000000) (1407573889 / 1000000000) (Real.log (2043015100423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2043015100423 / 500000000000) = -Real.log (500000000000 / 2043015100423) := by
    rw [show ((2043015100423 / 500000000000) : ℝ) = ((500000000000 / 2043015100423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (708127031 / 500000000) ≤ -Real.log (250000000000 / 1030413010021) ∧
    -Real.log (250000000000 / 1030413010021) ≤ (283250813 / 200000000) := by
  have h := checkLog_sound (w := (30413010021 / 2030413010021)) (n := 12)
    (lo := (14979851 / 500000000)) (hi := (29959703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030413010021 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1030413010021 / 1000000000000) = 1/(250000000000 / 1030413010021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (708127031 / 500000000) (283250813 / 200000000) (Real.log (1030413010021 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1030413010021 / 250000000000) = -Real.log (250000000000 / 1030413010021) := by
    rw [show ((1030413010021 / 250000000000) : ℝ) = ((250000000000 / 1030413010021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0026

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0027Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0027
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

theorem reflection_log_1_neg : (15715453 / 40000000) ≤ -Real.log (160 / 237) ∧
    -Real.log (160 / 237) ≤ (196443163 / 500000000) := by
  have h := checkLog_sound (w := (77 / 397)) (n := 12)
    (lo := (15715453 / 40000000)) (hi := (196443163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 160) = 1/(160 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (15715453 / 40000000) (196443163 / 500000000) (Real.log (237 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (237 / 160) = -Real.log (160 / 237) := by
    rw [show ((237 / 160) : ℝ) = ((160 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (656333207 / 1000000000) ≤ -Real.log (83 / 160) ∧
    -Real.log (83 / 160) ≤ (82041651 / 125000000) := by
  have h := checkLog_sound (w := (77 / 243)) (n := 12)
    (lo := (656333207 / 1000000000)) (hi := (82041651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 83) = 1/(83 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-82041651 / 125000000) (-656333207 / 1000000000) (Real.log (83 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (392094873 / 1000000000) ≤ -Real.log (2560 / 3789) ∧
    -Real.log (2560 / 3789) ≤ (196047437 / 500000000) := by
  have h := checkLog_sound (w := (1229 / 6349)) (n := 12)
    (lo := (392094873 / 1000000000)) (hi := (196047437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3789 / 2560) = 1/(2560 / 3789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (392094873 / 1000000000) (196047437 / 500000000) (Real.log (3789 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3789 / 2560) = -Real.log (2560 / 3789) := by
    rw [show ((3789 / 2560) : ℝ) = ((2560 / 3789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (654076719 / 1000000000) ≤ -Real.log (1331 / 2560) ∧
    -Real.log (1331 / 2560) ≤ (8175959 / 12500000) := by
  have h := checkLog_sound (w := (1229 / 3891)) (n := 12)
    (lo := (654076719 / 1000000000)) (hi := (8175959 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1331) = 1/(1331 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8175959 / 12500000) (-654076719 / 1000000000) (Real.log (1331 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67421917 / 100000000) ≤ -Real.log (80 / 157) ∧
    -Real.log (80 / 157) ≤ (674219171 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 237)) (n := 12)
    (lo := (67421917 / 100000000)) (hi := (674219171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 80) = 1/(80 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (67421917 / 100000000) (674219171 / 1000000000) (Real.log (157 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (157 / 80) = -Real.log (80 / 157) := by
    rw [show ((157 / 80) : ℝ) = ((80 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3283414343 / 1000000000) ≤ -Real.log (3 / 80) ∧
    -Real.log (3 / 80) ≤ (820853587 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 3) = 1/(3 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-820853587 / 250000000) (-3283414343 / 1000000000) (Real.log (3 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (673024189 / 1000000000) ≤ -Real.log (1280 / 2509) ∧
    -Real.log (1280 / 2509) ≤ (67302419 / 100000000) := by
  have h := checkLog_sound (w := (1229 / 3789)) (n := 12)
    (lo := (673024189 / 1000000000)) (hi := (67302419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1280) = 1/(1280 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (673024189 / 1000000000) (67302419 / 100000000) (Real.log (2509 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2509 / 1280) = -Real.log (1280 / 2509) := by
    rw [show ((2509 / 1280) : ℝ) = ((1280 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3222789721 / 1000000000) ≤ -Real.log (51 / 1280) ∧
    -Real.log (51 / 1280) ≤ (1611394863 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 51) = 1/(51 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1611394863 / 500000000) (-3222789721 / 1000000000) (Real.log (51 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137083381 / 250000000) ≤ -Real.log (1000000 / 1730367) ∧
    -Real.log (1000000 / 1730367) ≤ (21933341 / 40000000) := by
  have h := checkLog_sound (w := (730367 / 2730367)) (n := 12)
    (lo := (137083381 / 250000000)) (hi := (21933341 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1730367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1730367 / 1000000) = 1/(1000000 / 1730367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137083381 / 250000000) (21933341 / 40000000) (Real.log (1730367 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1730367 / 1000000) = -Real.log (1000000 / 1730367) := by
    rw [show ((1730367 / 1000000) : ℝ) = ((1000000 / 1730367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1310693503 / 1000000000) ≤ -Real.log (269633 / 1000000) ∧
    -Real.log (269633 / 1000000) ≤ (262138701 / 200000000) := by
  have h := checkLog_sound (w := (230367 / 769633)) (n := 12)
    (lo := (617546323 / 1000000000)) (hi := (154386581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 269633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 269633) = 1/(269633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-262138701 / 200000000) (-1310693503 / 1000000000) (Real.log (269633 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (137439843 / 250000000) ≤ -Real.log (250000 / 433209) ∧
    -Real.log (250000 / 433209) ≤ (549759373 / 1000000000) := by
  have h := checkLog_sound (w := (183209 / 683209)) (n := 12)
    (lo := (137439843 / 250000000)) (hi := (549759373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433209 / 250000) = 1/(250000 / 433209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (137439843 / 250000000) (549759373 / 1000000000) (Real.log (433209 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (433209 / 250000) = -Real.log (250000 / 433209) := by
    rw [show ((433209 / 250000) : ℝ) = ((250000 / 433209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41246643 / 31250000) ≤ -Real.log (66791 / 250000) ∧
    -Real.log (66791 / 250000) ≤ (659946289 / 500000000) := by
  have h := checkLog_sound (w := (58209 / 191791)) (n := 12)
    (lo := (156686349 / 250000000)) (hi := (626745397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 66791) = 1/(66791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-659946289 / 500000000) (-41246643 / 31250000) (Real.log (66791 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94508331 / 200000000) ≤ -Real.log (500000 / 802033) ∧
    -Real.log (500000 / 802033) ≤ (59067707 / 125000000) := by
  have h := checkLog_sound (w := (302033 / 1302033)) (n := 12)
    (lo := (94508331 / 200000000)) (hi := (59067707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802033 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802033 / 500000) = 1/(500000 / 802033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94508331 / 200000000) (59067707 / 125000000) (Real.log (802033 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (802033 / 500000) = -Real.log (500000 / 802033) := by
    rw [show ((802033 / 500000) : ℝ) = ((500000 / 802033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (926507747 / 1000000000) ≤ -Real.log (197967 / 500000) ∧
    -Real.log (197967 / 500000) ≤ (926507749 / 1000000000) := by
  have h := checkLog_sound (w := (52033 / 447967)) (n := 12)
    (lo := (233360567 / 1000000000)) (hi := (29170071 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 197967) = 1/(197967 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-926507749 / 1000000000) (-926507747 / 1000000000) (Real.log (197967 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94844817 / 200000000) ≤ -Real.log (1000000 / 1606767) ∧
    -Real.log (1000000 / 1606767) ≤ (237112043 / 500000000) := by
  have h := checkLog_sound (w := (606767 / 2606767)) (n := 12)
    (lo := (94844817 / 200000000)) (hi := (237112043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1606767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1606767 / 1000000) = 1/(1000000 / 1606767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94844817 / 200000000) (237112043 / 500000000) (Real.log (1606767 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1606767 / 1000000) = -Real.log (1000000 / 1606767) := by
    rw [show ((1606767 / 1000000) : ℝ) = ((1000000 / 1606767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (466676483 / 500000000) ≤ -Real.log (393233 / 1000000) ∧
    -Real.log (393233 / 1000000) ≤ (116669121 / 125000000) := by
  have h := checkLog_sound (w := (106767 / 893233)) (n := 12)
    (lo := (120102893 / 500000000)) (hi := (240205787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 393233) = 1/(393233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-116669121 / 125000000) (-466676483 / 500000000) (Real.log (393233 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1859027027 / 1000000000) ≤ -Real.log (12500000000 / 80218621237) ∧
    -Real.log (12500000000 / 80218621237) ≤ (185902703 / 100000000) := by
  have h := checkLog_sound (w := (30218621237 / 130218621237)) (n := 12)
    (lo := (472732667 / 1000000000)) (hi := (118183167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80218621237 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80218621237 / 50000000000) = 1/(12500000000 / 80218621237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1859027027 / 1000000000) (185902703 / 100000000) (Real.log (80218621237 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (80218621237 / 12500000000) = -Real.log (12500000000 / 80218621237) := by
    rw [show ((80218621237 / 12500000000) : ℝ) = ((12500000000 / 80218621237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (467412987 / 250000000) ≤ -Real.log (62500000000 / 405377408633) ∧
    -Real.log (62500000000 / 405377408633) ≤ (1869651951 / 1000000000) := by
  have h := checkLog_sound (w := (155377408633 / 655377408633)) (n := 12)
    (lo := (120839397 / 250000000)) (hi := (483357589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405377408633 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(405377408633 / 250000000000) = 1/(62500000000 / 405377408633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (467412987 / 250000000) (1869651951 / 1000000000) (Real.log (405377408633 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (405377408633 / 62500000000) = -Real.log (62500000000 / 405377408633) := by
    rw [show ((405377408633 / 62500000000) : ℝ) = ((62500000000 / 405377408633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (699524701 / 500000000) ≤ -Real.log (50000000000 / 202567347083) ∧
    -Real.log (50000000000 / 202567347083) ≤ (279809881 / 200000000) := by
  have h := checkLog_sound (w := (2567347083 / 402567347083)) (n := 12)
    (lo := (6377521 / 500000000)) (hi := (12755043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202567347083 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(202567347083 / 200000000000) = 1/(50000000000 / 202567347083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (699524701 / 500000000) (279809881 / 200000000) (Real.log (202567347083 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (202567347083 / 50000000000) = -Real.log (50000000000 / 202567347083) := by
    rw [show ((202567347083 / 50000000000) : ℝ) = ((50000000000 / 202567347083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1407577051 / 1000000000) ≤ -Real.log (250000000000 / 1021510783683) ∧
    -Real.log (250000000000 / 1021510783683) ≤ (703788527 / 500000000) := by
  have h := checkLog_sound (w := (21510783683 / 2021510783683)) (n := 12)
    (lo := (21282691 / 1000000000)) (hi := (5320673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021510783683 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1021510783683 / 1000000000000) = 1/(250000000000 / 1021510783683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1407577051 / 1000000000) (703788527 / 500000000) (Real.log (1021510783683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1021510783683 / 250000000000) = -Real.log (250000000000 / 1021510783683) := by
    rw [show ((1021510783683 / 250000000000) : ℝ) = ((250000000000 / 1021510783683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0027

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0028Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0028
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

theorem reflection_log_1_neg : (392094873 / 1000000000) ≤ -Real.log (2560 / 3789) ∧
    -Real.log (2560 / 3789) ≤ (196047437 / 500000000) := by
  have h := checkLog_sound (w := (1229 / 6349)) (n := 12)
    (lo := (392094873 / 1000000000)) (hi := (196047437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3789 / 2560) = 1/(2560 / 3789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (392094873 / 1000000000) (196047437 / 500000000) (Real.log (3789 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3789 / 2560) = -Real.log (2560 / 3789) := by
    rw [show ((3789 / 2560) : ℝ) = ((2560 / 3789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (654076719 / 1000000000) ≤ -Real.log (1331 / 2560) ∧
    -Real.log (1331 / 2560) ≤ (8175959 / 12500000) := by
  have h := checkLog_sound (w := (1229 / 3891)) (n := 12)
    (lo := (654076719 / 1000000000)) (hi := (8175959 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1331) = 1/(1331 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8175959 / 12500000) (-654076719 / 1000000000) (Real.log (1331 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (195651397 / 500000000) ≤ -Real.log (1280 / 1893) ∧
    -Real.log (1280 / 1893) ≤ (78260559 / 200000000) := by
  have h := checkLog_sound (w := (613 / 3173)) (n := 12)
    (lo := (195651397 / 500000000)) (hi := (78260559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1280) = 1/(1280 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (195651397 / 500000000) (78260559 / 200000000) (Real.log (1893 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1893 / 1280) = -Real.log (1280 / 1893) := by
    rw [show ((1893 / 1280) : ℝ) = ((1280 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65182531 / 100000000) ≤ -Real.log (667 / 1280) ∧
    -Real.log (667 / 1280) ≤ (651825311 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1947)) (n := 12)
    (lo := (65182531 / 100000000)) (hi := (651825311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 667) = 1/(667 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-651825311 / 1000000000) (-65182531 / 100000000) (Real.log (667 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (673024189 / 1000000000) ≤ -Real.log (1280 / 2509) ∧
    -Real.log (1280 / 2509) ≤ (67302419 / 100000000) := by
  have h := checkLog_sound (w := (1229 / 3789)) (n := 12)
    (lo := (673024189 / 1000000000)) (hi := (67302419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1280) = 1/(1280 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (673024189 / 1000000000) (67302419 / 100000000) (Real.log (2509 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2509 / 1280) = -Real.log (1280 / 2509) := by
    rw [show ((2509 / 1280) : ℝ) = ((1280 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3222789721 / 1000000000) ≤ -Real.log (51 / 1280) ∧
    -Real.log (51 / 1280) ≤ (1611394863 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 51) = 1/(51 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1611394863 / 500000000) (-3222789721 / 1000000000) (Real.log (51 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335913889 / 500000000) ≤ -Real.log (640 / 1253) ∧
    -Real.log (640 / 1253) ≤ (671827779 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1893)) (n := 12)
    (lo := (335913889 / 500000000)) (hi := (671827779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253 / 640) = 1/(640 / 1253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335913889 / 500000000) (671827779 / 1000000000) (Real.log (1253 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1253 / 640) = -Real.log (640 / 1253) := by
    rw [show ((1253 / 640) : ℝ) = ((640 / 1253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (791407827 / 250000000) ≤ -Real.log (27 / 640) ∧
    -Real.log (27 / 640) ≤ (3165631313 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 27) = 1/(27 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3165631313 / 1000000000) (-791407827 / 250000000) (Real.log (27 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (546920109 / 1000000000) ≤ -Real.log (1000000 / 1727923) ∧
    -Real.log (1000000 / 1727923) ≤ (54692011 / 100000000) := by
  have h := checkLog_sound (w := (727923 / 2727923)) (n := 12)
    (lo := (546920109 / 1000000000)) (hi := (54692011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1727923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1727923 / 1000000) = 1/(1000000 / 1727923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (546920109 / 1000000000) (54692011 / 100000000) (Real.log (1727923 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1727923 / 1000000) = -Real.log (1000000 / 1727923) := by
    rw [show ((1727923 / 1000000) : ℝ) = ((1000000 / 1727923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1301670163 / 1000000000) ≤ -Real.log (272077 / 1000000) ∧
    -Real.log (272077 / 1000000) ≤ (260334033 / 200000000) := by
  have h := checkLog_sound (w := (227923 / 772077)) (n := 12)
    (lo := (608522983 / 1000000000)) (hi := (76065373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 272077) = 1/(272077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-260334033 / 200000000) (-1301670163 / 1000000000) (Real.log (272077 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (274167051 / 500000000) ≤ -Real.log (15625 / 27037) ∧
    -Real.log (15625 / 27037) ≤ (548334103 / 1000000000) := by
  have h := checkLog_sound (w := (5706 / 21331)) (n := 12)
    (lo := (274167051 / 500000000)) (hi := (548334103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27037 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27037 / 15625) = 1/(15625 / 27037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (274167051 / 500000000) (548334103 / 1000000000) (Real.log (27037 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (27037 / 15625) = -Real.log (15625 / 27037) := by
    rw [show ((27037 / 15625) : ℝ) = ((15625 / 27037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (327674303 / 250000000) ≤ -Real.log (4213 / 15625) ∧
    -Real.log (4213 / 15625) ≤ (655348607 / 500000000) := by
  have h := checkLog_sound (w := (7199 / 24051)) (n := 12)
    (lo := (38596877 / 62500000)) (hi := (617550033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8426) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 8426) = 1/(4213 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-655348607 / 500000000) (-327674303 / 250000000) (Real.log (4213 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (235438811 / 500000000) ≤ -Real.log (1000000 / 1601399) ∧
    -Real.log (1000000 / 1601399) ≤ (470877623 / 1000000000) := by
  have h := checkLog_sound (w := (601399 / 2601399)) (n := 12)
    (lo := (235438811 / 500000000)) (hi := (470877623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1601399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1601399 / 1000000) = 1/(1000000 / 1601399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (235438811 / 500000000) (470877623 / 1000000000) (Real.log (1601399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1601399 / 1000000) = -Real.log (1000000 / 1601399) := by
    rw [show ((1601399 / 1000000) : ℝ) = ((1000000 / 1601399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (919794361 / 1000000000) ≤ -Real.log (398601 / 1000000) ∧
    -Real.log (398601 / 1000000) ≤ (919794363 / 1000000000) := by
  have h := checkLog_sound (w := (101399 / 898601)) (n := 12)
    (lo := (226647181 / 1000000000)) (hi := (113323591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 398601) = 1/(398601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-919794363 / 1000000000) (-919794361 / 1000000000) (Real.log (398601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (472542279 / 1000000000) ≤ -Real.log (1000000 / 1604067) ∧
    -Real.log (1000000 / 1604067) ≤ (11813557 / 25000000) := by
  have h := checkLog_sound (w := (604067 / 2604067)) (n := 12)
    (lo := (472542279 / 1000000000)) (hi := (11813557 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1604067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1604067 / 1000000) = 1/(1000000 / 1604067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (472542279 / 1000000000) (11813557 / 25000000) (Real.log (1604067 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1604067 / 1000000) = -Real.log (1000000 / 1604067) := by
    rw [show ((1604067 / 1000000) : ℝ) = ((1000000 / 1604067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (926510273 / 1000000000) ≤ -Real.log (395933 / 1000000) ∧
    -Real.log (395933 / 1000000) ≤ (37060411 / 40000000) := by
  have h := checkLog_sound (w := (104067 / 895933)) (n := 12)
    (lo := (233363093 / 1000000000)) (hi := (116681547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 395933) = 1/(395933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-37060411 / 40000000) (-926510273 / 1000000000) (Real.log (395933 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (28884223 / 15625000) ≤ -Real.log (500000000000 / 3175430117209) ∧
    -Real.log (500000000000 / 3175430117209) ≤ (73943611 / 40000000) := by
  have h := checkLog_sound (w := (1175430117209 / 5175430117209)) (n := 12)
    (lo := (57786989 / 125000000)) (hi := (462295913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3175430117209 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3175430117209 / 2000000000000) = 1/(500000000000 / 3175430117209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28884223 / 15625000) (73943611 / 40000000) (Real.log (3175430117209 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3175430117209 / 500000000000) = -Real.log (500000000000 / 3175430117209) := by
    rw [show ((3175430117209 / 500000000000) : ℝ) = ((500000000000 / 3175430117209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (929515657 / 500000000) ≤ -Real.log (3125000000 / 20054741277) ∧
    -Real.log (3125000000 / 20054741277) ≤ (1859031317 / 1000000000) := by
  have h := checkLog_sound (w := (7554741277 / 32554741277)) (n := 12)
    (lo := (236368477 / 500000000)) (hi := (94547391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20054741277 / 12500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20054741277 / 12500000000) = 1/(3125000000 / 20054741277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (929515657 / 500000000) (1859031317 / 1000000000) (Real.log (20054741277 / 3125000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20054741277 / 3125000000) = -Real.log (3125000000 / 20054741277) := by
    rw [show ((20054741277 / 3125000000) : ℝ) = ((3125000000 / 20054741277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1390671983 / 1000000000) ≤ -Real.log (500000000000 / 2008774438599) ∧
    -Real.log (500000000000 / 2008774438599) ≤ (695335993 / 500000000) := by
  have h := checkLog_sound (w := (8774438599 / 4008774438599)) (n := 12)
    (lo := (4377623 / 1000000000)) (hi := (547203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2008774438599 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2008774438599 / 2000000000000) = 1/(500000000000 / 2008774438599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1390671983 / 1000000000) (695335993 / 500000000) (Real.log (2008774438599 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2008774438599 / 500000000000) = -Real.log (500000000000 / 2008774438599) := by
    rw [show ((2008774438599 / 500000000000) : ℝ) = ((500000000000 / 2008774438599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1399052551 / 1000000000) ≤ -Real.log (250000000000 / 1012839924937) ∧
    -Real.log (250000000000 / 1012839924937) ≤ (699526277 / 500000000) := by
  have h := checkLog_sound (w := (12839924937 / 2012839924937)) (n := 12)
    (lo := (12758191 / 1000000000)) (hi := (797387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012839924937 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1012839924937 / 1000000000000) = 1/(250000000000 / 1012839924937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1399052551 / 1000000000) (699526277 / 500000000) (Real.log (1012839924937 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1012839924937 / 250000000000) = -Real.log (250000000000 / 1012839924937) := by
    rw [show ((1012839924937 / 250000000000) : ℝ) = ((250000000000 / 1012839924937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0028

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0029Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0029
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

theorem reflection_log_1_neg : (195651397 / 500000000) ≤ -Real.log (1280 / 1893) ∧
    -Real.log (1280 / 1893) ≤ (78260559 / 200000000) := by
  have h := checkLog_sound (w := (613 / 3173)) (n := 12)
    (lo := (195651397 / 500000000)) (hi := (78260559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1280) = 1/(1280 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (195651397 / 500000000) (78260559 / 200000000) (Real.log (1893 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1893 / 1280) = -Real.log (1280 / 1893) := by
    rw [show ((1893 / 1280) : ℝ) = ((1280 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65182531 / 100000000) ≤ -Real.log (667 / 1280) ∧
    -Real.log (667 / 1280) ≤ (651825311 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1947)) (n := 12)
    (lo := (65182531 / 100000000)) (hi := (651825311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 667) = 1/(667 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-651825311 / 1000000000) (-65182531 / 100000000) (Real.log (667 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (390510087 / 1000000000) ≤ -Real.log (2560 / 3783) ∧
    -Real.log (2560 / 3783) ≤ (48813761 / 125000000) := by
  have h := checkLog_sound (w := (1223 / 6343)) (n := 12)
    (lo := (390510087 / 1000000000)) (hi := (48813761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3783 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3783 / 2560) = 1/(2560 / 3783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (390510087 / 1000000000) (48813761 / 125000000) (Real.log (3783 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3783 / 2560) = -Real.log (2560 / 3783) := by
    rw [show ((3783 / 2560) : ℝ) = ((2560 / 3783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8119737 / 12500000) ≤ -Real.log (1337 / 2560) ∧
    -Real.log (1337 / 2560) ≤ (649578961 / 1000000000) := by
  have h := checkLog_sound (w := (1223 / 3897)) (n := 12)
    (lo := (8119737 / 12500000)) (hi := (649578961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1337) = 1/(1337 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-649578961 / 1000000000) (-8119737 / 12500000) (Real.log (1337 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335913889 / 500000000) ≤ -Real.log (640 / 1253) ∧
    -Real.log (640 / 1253) ≤ (671827779 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1893)) (n := 12)
    (lo := (335913889 / 500000000)) (hi := (671827779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253 / 640) = 1/(640 / 1253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335913889 / 500000000) (671827779 / 1000000000) (Real.log (1253 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1253 / 640) = -Real.log (640 / 1253) := by
    rw [show ((1253 / 640) : ℝ) = ((640 / 1253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (791407827 / 250000000) ≤ -Real.log (27 / 640) ∧
    -Real.log (27 / 640) ≤ (3165631313 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 27) = 1/(27 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3165631313 / 1000000000) (-791407827 / 250000000) (Real.log (27 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335314967 / 500000000) ≤ -Real.log (1280 / 2503) ∧
    -Real.log (1280 / 2503) ≤ (134125987 / 200000000) := by
  have h := checkLog_sound (w := (1223 / 3783)) (n := 12)
    (lo := (335314967 / 500000000)) (hi := (134125987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2503 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2503 / 1280) = 1/(1280 / 2503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335314967 / 500000000) (134125987 / 200000000) (Real.log (2503 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2503 / 1280) = -Real.log (1280 / 2503) := by
    rw [show ((2503 / 1280) : ℝ) = ((1280 / 2503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1555782043 / 500000000) ≤ -Real.log (57 / 1280) ∧
    -Real.log (57 / 1280) ≤ (3111564091 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 57) = 1/(57 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3111564091 / 1000000000) (-1555782043 / 500000000) (Real.log (57 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (545517443 / 1000000000) ≤ -Real.log (1000000 / 1725501) ∧
    -Real.log (1000000 / 1725501) ≤ (136379361 / 250000000) := by
  have h := checkLog_sound (w := (725501 / 2725501)) (n := 12)
    (lo := (545517443 / 1000000000)) (hi := (136379361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1725501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1725501 / 1000000) = 1/(1000000 / 1725501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (545517443 / 1000000000) (136379361 / 250000000) (Real.log (1725501 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1725501 / 1000000) = -Real.log (1000000 / 1725501) := by
    rw [show ((1725501 / 1000000) : ℝ) = ((1000000 / 1725501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (64640383 / 50000000) ≤ -Real.log (274499 / 1000000) ∧
    -Real.log (274499 / 1000000) ≤ (646403831 / 500000000) := by
  have h := checkLog_sound (w := (225501 / 774499)) (n := 12)
    (lo := (1873939 / 3125000)) (hi := (599660481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 274499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 274499) = 1/(274499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-646403831 / 500000000) (-64640383 / 50000000) (Real.log (274499 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (546920687 / 1000000000) ≤ -Real.log (250000 / 431981) ∧
    -Real.log (250000 / 431981) ≤ (34182543 / 62500000) := by
  have h := checkLog_sound (w := (181981 / 681981)) (n := 12)
    (lo := (546920687 / 1000000000)) (hi := (34182543 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431981 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431981 / 250000) = 1/(250000 / 431981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (546920687 / 1000000000) (34182543 / 62500000) (Real.log (431981 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (431981 / 250000) = -Real.log (250000 / 431981) := by
    rw [show ((431981 / 250000) : ℝ) = ((250000 / 431981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1301673839 / 1000000000) ≤ -Real.log (68019 / 250000) ∧
    -Real.log (68019 / 250000) ≤ (1301673841 / 1000000000) := by
  have h := checkLog_sound (w := (56981 / 193019)) (n := 12)
    (lo := (608526659 / 1000000000)) (hi := (30426333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68019) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 68019) = 1/(68019 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1301673841 / 1000000000) (-1301673839 / 1000000000) (Real.log (68019 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (93846041 / 200000000) ≤ -Real.log (1000000 / 1598763) ∧
    -Real.log (1000000 / 1598763) ≤ (234615103 / 500000000) := by
  have h := checkLog_sound (w := (598763 / 2598763)) (n := 12)
    (lo := (93846041 / 200000000)) (hi := (234615103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1598763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1598763 / 1000000) = 1/(1000000 / 1598763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (93846041 / 200000000) (234615103 / 500000000) (Real.log (1598763 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1598763 / 1000000) = -Real.log (1000000 / 1598763) := by
    rw [show ((1598763 / 1000000) : ℝ) = ((1000000 / 1598763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (913203003 / 1000000000) ≤ -Real.log (401237 / 1000000) ∧
    -Real.log (401237 / 1000000) ≤ (182640601 / 200000000) := by
  have h := checkLog_sound (w := (98763 / 901237)) (n := 12)
    (lo := (220055823 / 1000000000)) (hi := (13753489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 401237) = 1/(401237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-182640601 / 200000000) (-913203003 / 1000000000) (Real.log (401237 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (235439123 / 500000000) ≤ -Real.log (5000 / 8007) ∧
    -Real.log (5000 / 8007) ≤ (470878247 / 1000000000) := by
  have h := checkLog_sound (w := (3007 / 13007)) (n := 12)
    (lo := (235439123 / 500000000)) (hi := (470878247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8007 / 5000) = 1/(5000 / 8007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (235439123 / 500000000) (470878247 / 1000000000) (Real.log (8007 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (8007 / 5000) = -Real.log (5000 / 8007) := by
    rw [show ((8007 / 5000) : ℝ) = ((5000 / 8007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (91979687 / 100000000) ≤ -Real.log (1993 / 5000) ∧
    -Real.log (1993 / 5000) ≤ (114974609 / 125000000) := by
  have h := checkLog_sound (w := (507 / 4493)) (n := 12)
    (lo := (22664969 / 100000000)) (hi := (226649691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2500 / 1993) = 1/(1993 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-114974609 / 125000000) (-91979687 / 100000000) (Real.log (1993 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1838325103 / 1000000000) ≤ -Real.log (500000000000 / 3143000520949) ∧
    -Real.log (500000000000 / 3143000520949) ≤ (919162553 / 500000000) := by
  have h := checkLog_sound (w := (1143000520949 / 5143000520949)) (n := 12)
    (lo := (452030743 / 1000000000)) (hi := (56503843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3143000520949 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3143000520949 / 2000000000000) = 1/(500000000000 / 3143000520949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1838325103 / 1000000000) (919162553 / 500000000) (Real.log (3143000520949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3143000520949 / 500000000000) = -Real.log (500000000000 / 3143000520949) := by
    rw [show ((3143000520949 / 500000000000) : ℝ) = ((500000000000 / 3143000520949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (924297263 / 500000000) ≤ -Real.log (250000000000 / 1587721813023) ∧
    -Real.log (250000000000 / 1587721813023) ≤ (1848594529 / 1000000000) := by
  have h := checkLog_sound (w := (587721813023 / 2587721813023)) (n := 12)
    (lo := (231150083 / 500000000)) (hi := (462300167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587721813023 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1587721813023 / 1000000000000) = 1/(250000000000 / 1587721813023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (924297263 / 500000000) (1848594529 / 1000000000) (Real.log (1587721813023 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1587721813023 / 250000000000) = -Real.log (250000000000 / 1587721813023) := by
    rw [show ((1587721813023 / 250000000000) : ℝ) = ((250000000000 / 1587721813023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (172804151 / 125000000) ≤ -Real.log (25000000000 / 99614629259) ∧
    -Real.log (25000000000 / 99614629259) ≤ (138243321 / 100000000) := by
  have h := checkLog_sound (w := (49614629259 / 149614629259)) (n := 12)
    (lo := (172321507 / 250000000)) (hi := (689286029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99614629259 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(99614629259 / 50000000000) = 1/(25000000000 / 99614629259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (172804151 / 125000000) (138243321 / 100000000) (Real.log (99614629259 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (99614629259 / 25000000000) = -Real.log (25000000000 / 99614629259) := by
    rw [show ((99614629259 / 25000000000) : ℝ) = ((25000000000 / 99614629259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (347668779 / 250000000) ≤ -Real.log (125000000000 / 502195183141) ∧
    -Real.log (125000000000 / 502195183141) ≤ (1390675119 / 1000000000) := by
  have h := checkLog_sound (w := (2195183141 / 1002195183141)) (n := 12)
    (lo := (1095189 / 250000000)) (hi := (4380757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502195183141 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(502195183141 / 500000000000) = 1/(125000000000 / 502195183141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (347668779 / 250000000) (1390675119 / 1000000000) (Real.log (502195183141 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (502195183141 / 125000000000) = -Real.log (125000000000 / 502195183141) := by
    rw [show ((502195183141 / 125000000000) : ℝ) = ((125000000000 / 502195183141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0029

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0030Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0030
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

theorem reflection_log_1_neg : (390510087 / 1000000000) ≤ -Real.log (2560 / 3783) ∧
    -Real.log (2560 / 3783) ≤ (48813761 / 125000000) := by
  have h := checkLog_sound (w := (1223 / 6343)) (n := 12)
    (lo := (390510087 / 1000000000)) (hi := (48813761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3783 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3783 / 2560) = 1/(2560 / 3783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (390510087 / 1000000000) (48813761 / 125000000) (Real.log (3783 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3783 / 2560) = -Real.log (2560 / 3783) := by
    rw [show ((3783 / 2560) : ℝ) = ((2560 / 3783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8119737 / 12500000) ≤ -Real.log (1337 / 2560) ∧
    -Real.log (1337 / 2560) ≤ (649578961 / 1000000000) := by
  have h := checkLog_sound (w := (1223 / 3897)) (n := 12)
    (lo := (8119737 / 12500000)) (hi := (649578961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1337) = 1/(1337 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-649578961 / 1000000000) (-8119737 / 12500000) (Real.log (1337 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (389716751 / 1000000000) ≤ -Real.log (128 / 189) ∧
    -Real.log (128 / 189) ≤ (24357297 / 62500000) := by
  have h := checkLog_sound (w := (61 / 317)) (n := 12)
    (lo := (389716751 / 1000000000)) (hi := (24357297 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 128) = 1/(128 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (389716751 / 1000000000) (24357297 / 62500000) (Real.log (189 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (189 / 128) = -Real.log (128 / 189) := by
    rw [show ((189 / 128) : ℝ) = ((128 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (161834411 / 250000000) ≤ -Real.log (67 / 128) ∧
    -Real.log (67 / 128) ≤ (129467529 / 200000000) := by
  have h := checkLog_sound (w := (61 / 195)) (n := 12)
    (lo := (161834411 / 250000000)) (hi := (129467529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 67) = 1/(67 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129467529 / 200000000) (-161834411 / 250000000) (Real.log (67 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335314967 / 500000000) ≤ -Real.log (1280 / 2503) ∧
    -Real.log (1280 / 2503) ≤ (134125987 / 200000000) := by
  have h := checkLog_sound (w := (1223 / 3783)) (n := 12)
    (lo := (335314967 / 500000000)) (hi := (134125987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2503 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2503 / 1280) = 1/(1280 / 2503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335314967 / 500000000) (134125987 / 200000000) (Real.log (2503 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2503 / 1280) = -Real.log (1280 / 2503) := by
    rw [show ((2503 / 1280) : ℝ) = ((1280 / 2503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1555782043 / 500000000) ≤ -Real.log (57 / 1280) ∧
    -Real.log (57 / 1280) ≤ (3111564091 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 57) = 1/(57 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3111564091 / 1000000000) (-1555782043 / 500000000) (Real.log (57 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669430653 / 1000000000) (334715327 / 500000000) (Real.log (125 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (125 / 64) = -Real.log (64 / 125) := by
    rw [show ((125 / 64) : ℝ) = ((64 / 125) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (382533849 / 125000000) ≤ -Real.log (3 / 64) ∧
    -Real.log (3 / 64) ≤ (3060270797 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4 / 3) = 1/(3 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3060270797 / 1000000000) (-382533849 / 125000000) (Real.log (3 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (272062497 / 500000000) ≤ -Real.log (10000 / 17231) ∧
    -Real.log (10000 / 17231) ≤ (108824999 / 200000000) := by
  have h := checkLog_sound (w := (7231 / 27231)) (n := 12)
    (lo := (272062497 / 500000000)) (hi := (108824999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17231 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17231 / 10000) = 1/(10000 / 17231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (272062497 / 500000000) (108824999 / 200000000) (Real.log (17231 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (17231 / 10000) = -Real.log (10000 / 17231) := by
    rw [show ((17231 / 10000) : ℝ) = ((10000 / 17231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40128089 / 31250000) ≤ -Real.log (2769 / 10000) ∧
    -Real.log (2769 / 10000) ≤ (25681977 / 20000000) := by
  have h := checkLog_sound (w := (2231 / 7769)) (n := 12)
    (lo := (147737917 / 250000000)) (hi := (590951669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 2769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5000 / 2769) = 1/(2769 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25681977 / 20000000) (-40128089 / 31250000) (Real.log (2769 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (272759011 / 500000000) ≤ -Real.log (500000 / 862751) ∧
    -Real.log (500000 / 862751) ≤ (545518023 / 1000000000) := by
  have h := checkLog_sound (w := (362751 / 1362751)) (n := 12)
    (lo := (272759011 / 500000000)) (hi := (545518023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862751 / 500000) = 1/(500000 / 862751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (272759011 / 500000000) (545518023 / 1000000000) (Real.log (862751 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (862751 / 500000) = -Real.log (500000 / 862751) := by
    rw [show ((862751 / 500000) : ℝ) = ((500000 / 862751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1292811303 / 1000000000) ≤ -Real.log (137249 / 500000) ∧
    -Real.log (137249 / 500000) ≤ (258562261 / 200000000) := by
  have h := checkLog_sound (w := (112751 / 387249)) (n := 12)
    (lo := (599664123 / 1000000000)) (hi := (149916031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 137249) = 1/(137249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-258562261 / 200000000) (-1292811303 / 1000000000) (Real.log (137249 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116899403 / 250000000) ≤ -Real.log (200000 / 319231) ∧
    -Real.log (200000 / 319231) ≤ (467597613 / 1000000000) := by
  have h := checkLog_sound (w := (119231 / 519231)) (n := 12)
    (lo := (116899403 / 250000000)) (hi := (467597613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319231 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319231 / 200000) = 1/(200000 / 319231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116899403 / 250000000) (467597613 / 1000000000) (Real.log (319231 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (319231 / 200000) = -Real.log (200000 / 319231) := by
    rw [show ((319231 / 200000) : ℝ) = ((200000 / 319231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (906724137 / 1000000000) ≤ -Real.log (80769 / 200000) ∧
    -Real.log (80769 / 200000) ≤ (906724139 / 1000000000) := by
  have h := checkLog_sound (w := (19231 / 180769)) (n := 12)
    (lo := (213576957 / 1000000000)) (hi := (106788479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 80769) = 1/(80769 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-906724139 / 1000000000) (-906724137 / 1000000000) (Real.log (80769 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (46923083 / 100000000) ≤ -Real.log (250000 / 399691) ∧
    -Real.log (250000 / 399691) ≤ (469230831 / 1000000000) := by
  have h := checkLog_sound (w := (149691 / 649691)) (n := 12)
    (lo := (46923083 / 100000000)) (hi := (469230831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399691 / 250000) = 1/(250000 / 399691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46923083 / 100000000) (469230831 / 1000000000) (Real.log (399691 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399691 / 250000) = -Real.log (250000 / 399691) := by
    rw [show ((399691 / 250000) : ℝ) = ((250000 / 399691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182641099 / 200000000) ≤ -Real.log (100309 / 250000) ∧
    -Real.log (100309 / 250000) ≤ (913205497 / 1000000000) := by
  have h := checkLog_sound (w := (24691 / 225309)) (n := 12)
    (lo := (44011663 / 200000000)) (hi := (55014579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 100309) = 1/(100309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-913205497 / 1000000000) (-182641099 / 200000000) (Real.log (100309 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1828223841 / 1000000000) ≤ -Real.log (125000000000 / 777853015529) ∧
    -Real.log (125000000000 / 777853015529) ≤ (457055961 / 250000000) := by
  have h := checkLog_sound (w := (277853015529 / 1277853015529)) (n := 12)
    (lo := (441929481 / 1000000000)) (hi := (220964741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777853015529 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(777853015529 / 500000000000) = 1/(125000000000 / 777853015529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1828223841 / 1000000000) (457055961 / 250000000) (Real.log (777853015529 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (777853015529 / 125000000000) = -Real.log (125000000000 / 777853015529) := by
    rw [show ((777853015529 / 125000000000) : ℝ) = ((125000000000 / 777853015529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73533173 / 40000000) ≤ -Real.log (500000000000 / 3143013792451) ∧
    -Real.log (500000000000 / 3143013792451) ≤ (114895583 / 62500000) := by
  have h := checkLog_sound (w := (1143013792451 / 5143013792451)) (n := 12)
    (lo := (90406993 / 200000000)) (hi := (226017483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3143013792451 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3143013792451 / 2000000000000) = 1/(500000000000 / 3143013792451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73533173 / 40000000) (114895583 / 62500000) (Real.log (3143013792451 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3143013792451 / 500000000000) = -Real.log (500000000000 / 3143013792451) := by
    rw [show ((3143013792451 / 500000000000) : ℝ) = ((500000000000 / 3143013792451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1374321749 / 1000000000) ≤ -Real.log (1562500000 / 6175617347) ∧
    -Real.log (1562500000 / 6175617347) ≤ (1374321751 / 1000000000) := by
  have h := checkLog_sound (w := (3050617347 / 9300617347)) (n := 12)
    (lo := (681174569 / 1000000000)) (hi := (68117457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6175617347 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6175617347 / 3125000000) = 1/(1562500000 / 6175617347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1374321749 / 1000000000) (1374321751 / 1000000000) (Real.log (6175617347 / 1562500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6175617347 / 1562500000) = -Real.log (1562500000 / 6175617347) := by
    rw [show ((6175617347 / 1562500000) : ℝ) = ((1562500000 / 6175617347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (691218163 / 500000000) ≤ -Real.log (500000000000 / 1992298796719) ∧
    -Real.log (500000000000 / 1992298796719) ≤ (172804541 / 125000000) := by
  have h := checkLog_sound (w := (992298796719 / 2992298796719)) (n := 12)
    (lo := (344644573 / 500000000)) (hi := (689289147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1992298796719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1992298796719 / 1000000000000) = 1/(500000000000 / 1992298796719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (691218163 / 500000000) (172804541 / 125000000) (Real.log (1992298796719 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1992298796719 / 500000000000) = -Real.log (500000000000 / 1992298796719) := by
    rw [show ((1992298796719 / 500000000000) : ℝ) = ((500000000000 / 1992298796719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0030

end


