-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0093Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0093Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:29:23.233989+00:00
-- url     : https://prove2.me/theorems/0b6adc03-ae20-4c28-b02b-044f4e9c4f82
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0093Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0094Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0093Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0098Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0099Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0093Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0098Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0099Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0093Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0094Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0095Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0096Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0097Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0098Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0099Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0093Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0094Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0095Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0096Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0097Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0098Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0099Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0093Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0093
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

theorem reflection_log_1_neg : (339258529 / 1000000000) ≤ -Real.log (1280 / 1797) ∧
    -Real.log (1280 / 1797) ≤ (33925853 / 100000000) := by
  have h := checkLog_sound (w := (517 / 3077)) (n := 12)
    (lo := (339258529 / 1000000000)) (hi := (33925853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1797 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1797 / 1280) = 1/(1280 / 1797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (339258529 / 1000000000) (33925853 / 100000000) (Real.log (1797 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1797 / 1280) = -Real.log (1280 / 1797) := by
    rw [show ((1797 / 1280) : ℝ) = ((1280 / 1797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20694293 / 40000000) ≤ -Real.log (763 / 1280) ∧
    -Real.log (763 / 1280) ≤ (258678663 / 500000000) := by
  have h := checkLog_sound (w := (517 / 2043)) (n := 12)
    (lo := (20694293 / 40000000)) (hi := (258678663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 763) = 1/(763 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-258678663 / 500000000) (-20694293 / 40000000) (Real.log (763 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10575733 / 31250000) ≤ -Real.log (2560 / 3591) ∧
    -Real.log (2560 / 3591) ≤ (338423457 / 1000000000) := by
  have h := checkLog_sound (w := (1031 / 6151)) (n := 12)
    (lo := (10575733 / 31250000)) (hi := (338423457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3591 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3591 / 2560) = 1/(2560 / 3591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10575733 / 31250000) (338423457 / 1000000000) (Real.log (3591 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3591 / 2560) = -Real.log (2560 / 3591) := by
    rw [show ((3591 / 2560) : ℝ) = ((2560 / 3591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (515393331 / 1000000000) ≤ -Real.log (1529 / 2560) ∧
    -Real.log (1529 / 2560) ≤ (128848333 / 250000000) := by
  have h := checkLog_sound (w := (1031 / 4089)) (n := 12)
    (lo := (515393331 / 1000000000)) (hi := (128848333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1529) = 1/(1529 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-128848333 / 250000000) (-515393331 / 1000000000) (Real.log (1529 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (590820253 / 1000000000) ≤ -Real.log (1280 / 2311) ∧
    -Real.log (1280 / 2311) ≤ (295410127 / 500000000) := by
  have h := checkLog_sound (w := (1031 / 3591)) (n := 12)
    (lo := (590820253 / 1000000000)) (hi := (295410127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 1280) = 1/(1280 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (590820253 / 1000000000) (295410127 / 500000000) (Real.log (2311 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2311 / 1280) = -Real.log (1280 / 2311) := by
    rw [show ((2311 / 1280) : ℝ) = ((1280 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1637162459 / 1000000000) ≤ -Real.log (249 / 1280) ∧
    -Real.log (249 / 1280) ≤ (818581231 / 500000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 249) = 1/(249 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-818581231 / 500000000) (-1637162459 / 1000000000) (Real.log (249 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (464813307 / 1000000000) ≤ -Real.log (1000000 / 1591717) ∧
    -Real.log (1000000 / 1591717) ≤ (116203327 / 250000000) := by
  have h := checkLog_sound (w := (591717 / 2591717)) (n := 12)
    (lo := (464813307 / 1000000000)) (hi := (116203327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1591717 / 1000000) = 1/(1000000 / 1591717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (464813307 / 1000000000) (116203327 / 250000000) (Real.log (1591717 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1591717 / 1000000) = -Real.log (1000000 / 1591717) := by
    rw [show ((1591717 / 1000000) : ℝ) = ((1000000 / 1591717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (895794717 / 1000000000) ≤ -Real.log (408283 / 1000000) ∧
    -Real.log (408283 / 1000000) ≤ (895794719 / 1000000000) := by
  have h := checkLog_sound (w := (91717 / 908283)) (n := 12)
    (lo := (202647537 / 1000000000)) (hi := (101323769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 408283) = 1/(408283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-895794719 / 1000000000) (-895794717 / 1000000000) (Real.log (408283 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (116504863 / 250000000) ≤ -Real.log (500000 / 796819) ∧
    -Real.log (500000 / 796819) ≤ (466019453 / 1000000000) := by
  have h := checkLog_sound (w := (296819 / 1296819)) (n := 12)
    (lo := (116504863 / 250000000)) (hi := (466019453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796819 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796819 / 500000) = 1/(500000 / 796819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (116504863 / 250000000) (466019453 / 1000000000) (Real.log (796819 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (796819 / 500000) = -Real.log (500000 / 796819) := by
    rw [show ((796819 / 500000) : ℝ) = ((500000 / 796819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90051089 / 100000000) ≤ -Real.log (203181 / 500000) ∧
    -Real.log (203181 / 500000) ≤ (225127723 / 250000000) := by
  have h := checkLog_sound (w := (46819 / 453181)) (n := 12)
    (lo := (20736371 / 100000000)) (hi := (207363711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 203181) = 1/(203181 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225127723 / 250000000) (-90051089 / 100000000) (Real.log (203181 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190232599 / 500000000) ≤ -Real.log (200000 / 292593) ∧
    -Real.log (200000 / 292593) ≤ (380465199 / 1000000000) := by
  have h := checkLog_sound (w := (92593 / 492593)) (n := 12)
    (lo := (190232599 / 500000000)) (hi := (380465199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292593 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292593 / 200000) = 1/(200000 / 292593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190232599 / 500000000) (380465199 / 1000000000) (Real.log (292593 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (292593 / 200000) = -Real.log (200000 / 292593) := by
    rw [show ((292593 / 200000) : ℝ) = ((200000 / 292593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (621692009 / 1000000000) ≤ -Real.log (107407 / 200000) ∧
    -Real.log (107407 / 200000) ≤ (62169201 / 100000000) := by
  have h := checkLog_sound (w := (92593 / 307407)) (n := 12)
    (lo := (621692009 / 1000000000)) (hi := (62169201 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 107407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 107407) = 1/(107407 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62169201 / 100000000) (-621692009 / 1000000000) (Real.log (107407 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95427289 / 250000000) ≤ -Real.log (500000 / 732393) ∧
    -Real.log (500000 / 732393) ≤ (381709157 / 1000000000) := by
  have h := checkLog_sound (w := (232393 / 1232393)) (n := 12)
    (lo := (95427289 / 250000000)) (hi := (381709157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732393 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732393 / 500000) = 1/(500000 / 732393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95427289 / 250000000) (381709157 / 1000000000) (Real.log (732393 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (732393 / 500000) = -Real.log (500000 / 732393) := by
    rw [show ((732393 / 500000) : ℝ) = ((500000 / 732393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156272153 / 250000000) ≤ -Real.log (267607 / 500000) ∧
    -Real.log (267607 / 500000) ≤ (625088613 / 1000000000) := by
  have h := checkLog_sound (w := (232393 / 767607)) (n := 12)
    (lo := (156272153 / 250000000)) (hi := (625088613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 267607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 267607) = 1/(267607 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-625088613 / 1000000000) (-156272153 / 250000000) (Real.log (267607 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (170076003 / 125000000) ≤ -Real.log (500000000000 / 1949281503271) ∧
    -Real.log (500000000000 / 1949281503271) ≤ (680304013 / 500000000) := by
  have h := checkLog_sound (w := (949281503271 / 2949281503271)) (n := 12)
    (lo := (166865211 / 250000000)) (hi := (133492169 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949281503271 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1949281503271 / 1000000000000) = 1/(500000000000 / 1949281503271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (170076003 / 125000000) (680304013 / 500000000) (Real.log (1949281503271 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1949281503271 / 500000000000) = -Real.log (500000000000 / 1949281503271) := by
    rw [show ((1949281503271 / 500000000000) : ℝ) = ((500000000000 / 1949281503271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1366530343 / 1000000000) ≤ -Real.log (500000000000 / 1960860021361) ∧
    -Real.log (500000000000 / 1960860021361) ≤ (273306069 / 200000000) := by
  have h := checkLog_sound (w := (960860021361 / 2960860021361)) (n := 12)
    (lo := (673383163 / 1000000000)) (hi := (168345791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960860021361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960860021361 / 1000000000000) = 1/(500000000000 / 1960860021361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1366530343 / 1000000000) (273306069 / 200000000) (Real.log (1960860021361 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1960860021361 / 500000000000) = -Real.log (500000000000 / 1960860021361) := by
    rw [show ((1960860021361 / 500000000000) : ℝ) = ((500000000000 / 1960860021361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1002157207 / 1000000000) ≤ -Real.log (125000000000 / 340519007141) ∧
    -Real.log (125000000000 / 340519007141) ≤ (1002157209 / 1000000000) := by
  have h := checkLog_sound (w := (90519007141 / 590519007141)) (n := 12)
    (lo := (309010027 / 1000000000)) (hi := (77252507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340519007141 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(340519007141 / 250000000000) = 1/(125000000000 / 340519007141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1002157207 / 1000000000) (1002157209 / 1000000000) (Real.log (340519007141 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (340519007141 / 125000000000) = -Real.log (125000000000 / 340519007141) := by
    rw [show ((340519007141 / 125000000000) : ℝ) = ((125000000000 / 340519007141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (125849721 / 125000000) ≤ -Real.log (5000000000 / 13684115139) ∧
    -Real.log (5000000000 / 13684115139) ≤ (100679777 / 100000000) := by
  have h := checkLog_sound (w := (3684115139 / 23684115139)) (n := 12)
    (lo := (78412647 / 250000000)) (hi := (313650589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13684115139 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13684115139 / 10000000000) = 1/(5000000000 / 13684115139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (125849721 / 125000000) (100679777 / 100000000) (Real.log (13684115139 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13684115139 / 5000000000) = -Real.log (5000000000 / 13684115139) := by
    rw [show ((13684115139 / 5000000000) : ℝ) = ((5000000000 / 13684115139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0093

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0094Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0094
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

theorem reflection_log_1_neg : (10575733 / 31250000) ≤ -Real.log (2560 / 3591) ∧
    -Real.log (2560 / 3591) ≤ (338423457 / 1000000000) := by
  have h := checkLog_sound (w := (1031 / 6151)) (n := 12)
    (lo := (10575733 / 31250000)) (hi := (338423457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3591 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3591 / 2560) = 1/(2560 / 3591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10575733 / 31250000) (338423457 / 1000000000) (Real.log (3591 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3591 / 2560) = -Real.log (2560 / 3591) := by
    rw [show ((3591 / 2560) : ℝ) = ((2560 / 3591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (515393331 / 1000000000) ≤ -Real.log (1529 / 2560) ∧
    -Real.log (1529 / 2560) ≤ (128848333 / 250000000) := by
  have h := checkLog_sound (w := (1031 / 4089)) (n := 12)
    (lo := (515393331 / 1000000000)) (hi := (128848333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1529) = 1/(1529 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-128848333 / 250000000) (-515393331 / 1000000000) (Real.log (1529 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67517537 / 200000000) ≤ -Real.log (640 / 897) ∧
    -Real.log (640 / 897) ≤ (168793843 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1537)) (n := 12)
    (lo := (67517537 / 200000000)) (hi := (168793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897 / 640) = 1/(640 / 897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67517537 / 200000000) (168793843 / 500000000) (Real.log (897 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (897 / 640) = -Real.log (640 / 897) := by
    rw [show ((897 / 640) : ℝ) = ((640 / 897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (513433187 / 1000000000) ≤ -Real.log (383 / 640) ∧
    -Real.log (383 / 640) ≤ (128358297 / 250000000) := by
  have h := checkLog_sound (w := (257 / 1023)) (n := 12)
    (lo := (513433187 / 1000000000)) (hi := (128358297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 383) = 1/(383 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-128358297 / 250000000) (-513433187 / 1000000000) (Real.log (383 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (590820253 / 1000000000) ≤ -Real.log (1280 / 2311) ∧
    -Real.log (1280 / 2311) ≤ (295410127 / 500000000) := by
  have h := checkLog_sound (w := (1031 / 3591)) (n := 12)
    (lo := (590820253 / 1000000000)) (hi := (295410127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 1280) = 1/(1280 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (590820253 / 1000000000) (295410127 / 500000000) (Real.log (2311 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2311 / 1280) = -Real.log (1280 / 2311) := by
    rw [show ((2311 / 1280) : ℝ) = ((1280 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1637162459 / 1000000000) ≤ -Real.log (249 / 1280) ∧
    -Real.log (249 / 1280) ≤ (818581231 / 500000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 249) = 1/(249 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-818581231 / 500000000) (-1637162459 / 1000000000) (Real.log (249 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (58952127 / 100000000) ≤ -Real.log (320 / 577) ∧
    -Real.log (320 / 577) ≤ (589521271 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 897)) (n := 12)
    (lo := (58952127 / 100000000)) (hi := (589521271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 320) = 1/(320 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (58952127 / 100000000) (589521271 / 1000000000) (Real.log (577 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (577 / 320) = -Real.log (320 / 577) := by
    rw [show ((577 / 320) : ℝ) = ((320 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (406296567 / 250000000) ≤ -Real.log (63 / 320) ∧
    -Real.log (63 / 320) ≤ (1625186271 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 63) = 1/(63 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1625186271 / 1000000000) (-406296567 / 250000000) (Real.log (63 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (231804111 / 500000000) ≤ -Real.log (5000 / 7949) ∧
    -Real.log (5000 / 7949) ≤ (463608223 / 1000000000) := by
  have h := checkLog_sound (w := (2949 / 12949)) (n := 12)
    (lo := (231804111 / 500000000)) (hi := (463608223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7949 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7949 / 5000) = 1/(5000 / 7949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (231804111 / 500000000) (463608223 / 1000000000) (Real.log (7949 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (7949 / 5000) = -Real.log (5000 / 7949) := by
    rw [show ((7949 / 5000) : ℝ) = ((5000 / 7949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27847201 / 31250000) ≤ -Real.log (2051 / 5000) ∧
    -Real.log (2051 / 5000) ≤ (445555217 / 500000000) := by
  have h := checkLog_sound (w := (449 / 4551)) (n := 12)
    (lo := (49490813 / 250000000)) (hi := (197963253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2051) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2500 / 2051) = 1/(2051 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-445555217 / 500000000) (-27847201 / 31250000) (Real.log (2051 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29050871 / 62500000) ≤ -Real.log (500000 / 795859) ∧
    -Real.log (500000 / 795859) ≤ (464813937 / 1000000000) := by
  have h := checkLog_sound (w := (295859 / 1295859)) (n := 12)
    (lo := (29050871 / 62500000)) (hi := (464813937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795859 / 500000) = 1/(500000 / 795859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29050871 / 62500000) (464813937 / 1000000000) (Real.log (795859 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (795859 / 500000) = -Real.log (500000 / 795859) := by
    rw [show ((795859 / 500000) : ℝ) = ((500000 / 795859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (447898583 / 500000000) ≤ -Real.log (204141 / 500000) ∧
    -Real.log (204141 / 500000) ≤ (55987323 / 62500000) := by
  have h := checkLog_sound (w := (45859 / 454141)) (n := 12)
    (lo := (101324993 / 500000000)) (hi := (202649987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 204141) = 1/(204141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55987323 / 62500000) (-447898583 / 500000000) (Real.log (204141 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (379224481 / 1000000000) ≤ -Real.log (1000000 / 1461151) ∧
    -Real.log (1000000 / 1461151) ≤ (189612241 / 500000000) := by
  have h := checkLog_sound (w := (461151 / 2461151)) (n := 12)
    (lo := (379224481 / 1000000000)) (hi := (189612241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461151 / 1000000) = 1/(1000000 / 1461151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (379224481 / 1000000000) (189612241 / 500000000) (Real.log (1461151 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1461151 / 1000000) = -Real.log (1000000 / 1461151) := by
    rw [show ((1461151 / 1000000) : ℝ) = ((1000000 / 1461151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (123663979 / 200000000) ≤ -Real.log (538849 / 1000000) ∧
    -Real.log (538849 / 1000000) ≤ (77289987 / 125000000) := by
  have h := checkLog_sound (w := (461151 / 1538849)) (n := 12)
    (lo := (123663979 / 200000000)) (hi := (77289987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 538849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 538849) = 1/(538849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77289987 / 125000000) (-123663979 / 200000000) (Real.log (538849 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (380465881 / 1000000000) ≤ -Real.log (500000 / 731483) ∧
    -Real.log (500000 / 731483) ≤ (190232941 / 500000000) := by
  have h := checkLog_sound (w := (231483 / 1231483)) (n := 12)
    (lo := (380465881 / 1000000000)) (hi := (190232941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731483 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731483 / 500000) = 1/(500000 / 731483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (380465881 / 1000000000) (190232941 / 500000000) (Real.log (731483 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (731483 / 500000) = -Real.log (500000 / 731483) := by
    rw [show ((731483 / 500000) : ℝ) = ((500000 / 731483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (621693871 / 1000000000) ≤ -Real.log (268517 / 500000) ∧
    -Real.log (268517 / 500000) ≤ (38855867 / 62500000) := by
  have h := checkLog_sound (w := (231483 / 768517)) (n := 12)
    (lo := (621693871 / 1000000000)) (hi := (38855867 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 268517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 268517) = 1/(268517 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-38855867 / 62500000) (-621693871 / 1000000000) (Real.log (268517 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (677359327 / 500000000) ≤ -Real.log (25000000000 / 96891760117) ∧
    -Real.log (25000000000 / 96891760117) ≤ (21167479 / 15625000) := by
  have h := checkLog_sound (w := (46891760117 / 146891760117)) (n := 12)
    (lo := (330785737 / 500000000)) (hi := (26462859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96891760117 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96891760117 / 50000000000) = 1/(25000000000 / 96891760117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (677359327 / 500000000) (21167479 / 15625000) (Real.log (96891760117 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (96891760117 / 25000000000) = -Real.log (25000000000 / 96891760117) := by
    rw [show ((96891760117 / 25000000000) : ℝ) = ((25000000000 / 96891760117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (680305551 / 500000000) ≤ -Real.log (250000000000 / 974643751133) ∧
    -Real.log (250000000000 / 974643751133) ≤ (42519097 / 31250000) := by
  have h := checkLog_sound (w := (474643751133 / 1474643751133)) (n := 12)
    (lo := (333731961 / 500000000)) (hi := (667463923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974643751133 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(974643751133 / 500000000000) = 1/(250000000000 / 974643751133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (680305551 / 500000000) (42519097 / 31250000) (Real.log (974643751133 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (974643751133 / 250000000000) = -Real.log (250000000000 / 974643751133) := by
    rw [show ((974643751133 / 250000000000) : ℝ) = ((250000000000 / 974643751133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (124693047 / 125000000) ≤ -Real.log (500000000000 / 1355807471109) ∧
    -Real.log (500000000000 / 1355807471109) ≤ (498772189 / 500000000) := by
  have h := checkLog_sound (w := (355807471109 / 2355807471109)) (n := 12)
    (lo := (76099299 / 250000000)) (hi := (304397197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355807471109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1355807471109 / 1000000000000) = 1/(500000000000 / 1355807471109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (124693047 / 125000000) (498772189 / 500000000) (Real.log (1355807471109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1355807471109 / 500000000000) = -Real.log (500000000000 / 1355807471109) := by
    rw [show ((1355807471109 / 500000000000) : ℝ) = ((500000000000 / 1355807471109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1002159753 / 1000000000) ≤ -Real.log (250000000000 / 681039747949) ∧
    -Real.log (250000000000 / 681039747949) ≤ (200431951 / 200000000) := by
  have h := checkLog_sound (w := (181039747949 / 1181039747949)) (n := 12)
    (lo := (309012573 / 1000000000)) (hi := (154506287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681039747949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(681039747949 / 500000000000) = 1/(250000000000 / 681039747949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1002159753 / 1000000000) (200431951 / 200000000) (Real.log (681039747949 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (681039747949 / 250000000000) = -Real.log (250000000000 / 681039747949) := by
    rw [show ((681039747949 / 250000000000) : ℝ) = ((250000000000 / 681039747949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0094

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0095Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0095
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

theorem reflection_log_1_neg : (67517537 / 200000000) ≤ -Real.log (640 / 897) ∧
    -Real.log (640 / 897) ≤ (168793843 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1537)) (n := 12)
    (lo := (67517537 / 200000000)) (hi := (168793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897 / 640) = 1/(640 / 897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67517537 / 200000000) (168793843 / 500000000) (Real.log (897 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (897 / 640) = -Real.log (640 / 897) := by
    rw [show ((897 / 640) : ℝ) = ((640 / 897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (513433187 / 1000000000) ≤ -Real.log (383 / 640) ∧
    -Real.log (383 / 640) ≤ (128358297 / 250000000) := by
  have h := checkLog_sound (w := (257 / 1023)) (n := 12)
    (lo := (513433187 / 1000000000)) (hi := (128358297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 383) = 1/(383 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-128358297 / 250000000) (-513433187 / 1000000000) (Real.log (383 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67350243 / 200000000) ≤ -Real.log (512 / 717) ∧
    -Real.log (512 / 717) ≤ (21046951 / 62500000) := by
  have h := checkLog_sound (w := (205 / 1229)) (n := 12)
    (lo := (67350243 / 200000000)) (hi := (21046951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 512) = 1/(512 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67350243 / 200000000) (21046951 / 62500000) (Real.log (717 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (717 / 512) = -Real.log (512 / 717) := by
    rw [show ((717 / 512) : ℝ) = ((512 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (511476877 / 1000000000) ≤ -Real.log (307 / 512) ∧
    -Real.log (307 / 512) ≤ (255738439 / 500000000) := by
  have h := checkLog_sound (w := (205 / 819)) (n := 12)
    (lo := (511476877 / 1000000000)) (hi := (255738439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 307) = 1/(307 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-255738439 / 500000000) (-511476877 / 1000000000) (Real.log (307 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (58952127 / 100000000) ≤ -Real.log (320 / 577) ∧
    -Real.log (320 / 577) ≤ (589521271 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 897)) (n := 12)
    (lo := (58952127 / 100000000)) (hi := (589521271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 320) = 1/(320 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (58952127 / 100000000) (589521271 / 1000000000) (Real.log (577 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (577 / 320) = -Real.log (320 / 577) := by
    rw [show ((577 / 320) : ℝ) = ((320 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (406296567 / 250000000) ≤ -Real.log (63 / 320) ∧
    -Real.log (63 / 320) ≤ (1625186271 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 63) = 1/(63 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1625186271 / 1000000000) (-406296567 / 250000000) (Real.log (63 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (294110299 / 500000000) ≤ -Real.log (256 / 461) ∧
    -Real.log (256 / 461) ≤ (588220599 / 1000000000) := by
  have h := checkLog_sound (w := (205 / 717)) (n := 12)
    (lo := (294110299 / 500000000)) (hi := (588220599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 256) = 1/(256 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (294110299 / 500000000) (588220599 / 1000000000) (Real.log (461 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (461 / 256) = -Real.log (256 / 461) := by
    rw [show ((461 / 256) : ℝ) = ((256 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (161335181 / 100000000) ≤ -Real.log (51 / 256) ∧
    -Real.log (51 / 256) ≤ (1613351813 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 51) = 1/(51 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1613351813 / 1000000000) (-161335181 / 100000000) (Real.log (51 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (231201471 / 500000000) ≤ -Real.log (200000 / 317577) ∧
    -Real.log (200000 / 317577) ≤ (462402943 / 1000000000) := by
  have h := checkLog_sound (w := (117577 / 517577)) (n := 12)
    (lo := (231201471 / 500000000)) (hi := (462402943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317577 / 200000) = 1/(200000 / 317577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (231201471 / 500000000) (462402943 / 1000000000) (Real.log (317577 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (317577 / 200000) = -Real.log (200000 / 317577) := by
    rw [show ((317577 / 200000) : ℝ) = ((200000 / 317577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (886452841 / 1000000000) ≤ -Real.log (82423 / 200000) ∧
    -Real.log (82423 / 200000) ≤ (886452843 / 1000000000) := by
  have h := checkLog_sound (w := (17577 / 182423)) (n := 12)
    (lo := (193305661 / 1000000000)) (hi := (96652831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 82423) = 1/(82423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-886452843 / 1000000000) (-886452841 / 1000000000) (Real.log (82423 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (463608851 / 1000000000) ≤ -Real.log (1000000 / 1589801) ∧
    -Real.log (1000000 / 1589801) ≤ (115902213 / 250000000) := by
  have h := checkLog_sound (w := (589801 / 2589801)) (n := 12)
    (lo := (463608851 / 1000000000)) (hi := (115902213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1589801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1589801 / 1000000) = 1/(1000000 / 1589801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (463608851 / 1000000000) (115902213 / 250000000) (Real.log (1589801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1589801 / 1000000) = -Real.log (1000000 / 1589801) := by
    rw [show ((1589801 / 1000000) : ℝ) = ((1000000 / 1589801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89111287 / 100000000) ≤ -Real.log (410199 / 1000000) ∧
    -Real.log (410199 / 1000000) ≤ (111389109 / 125000000) := by
  have h := checkLog_sound (w := (89801 / 910199)) (n := 12)
    (lo := (19796569 / 100000000)) (hi := (197965691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 410199) = 1/(410199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111389109 / 125000000) (-89111287 / 100000000) (Real.log (410199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (377987019 / 1000000000) ≤ -Real.log (62500 / 91209) ∧
    -Real.log (62500 / 91209) ≤ (18899351 / 50000000) := by
  have h := checkLog_sound (w := (28709 / 153709)) (n := 12)
    (lo := (377987019 / 1000000000)) (hi := (18899351 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91209 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91209 / 62500) = 1/(62500 / 91209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (377987019 / 1000000000) (18899351 / 50000000) (Real.log (91209 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (91209 / 62500) = -Real.log (62500 / 91209) := by
    rw [show ((91209 / 62500) : ℝ) = ((62500 / 91209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (614972061 / 1000000000) ≤ -Real.log (33791 / 62500) ∧
    -Real.log (33791 / 62500) ≤ (307486031 / 500000000) := by
  have h := checkLog_sound (w := (28709 / 96291)) (n := 12)
    (lo := (614972061 / 1000000000)) (hi := (307486031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33791) = 1/(33791 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-307486031 / 500000000) (-614972061 / 1000000000) (Real.log (33791 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (75845033 / 200000000) ≤ -Real.log (31250 / 45661) ∧
    -Real.log (31250 / 45661) ≤ (189612583 / 500000000) := by
  have h := checkLog_sound (w := (14411 / 76911)) (n := 12)
    (lo := (75845033 / 200000000)) (hi := (189612583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45661 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45661 / 31250) = 1/(31250 / 45661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75845033 / 200000000) (189612583 / 500000000) (Real.log (45661 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (45661 / 31250) = -Real.log (31250 / 45661) := by
    rw [show ((45661 / 31250) : ℝ) = ((31250 / 45661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (618321751 / 1000000000) ≤ -Real.log (16839 / 31250) ∧
    -Real.log (16839 / 31250) ≤ (77290219 / 125000000) := by
  have h := checkLog_sound (w := (14411 / 48089)) (n := 12)
    (lo := (618321751 / 1000000000)) (hi := (77290219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 16839) = 1/(16839 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77290219 / 125000000) (-618321751 / 1000000000) (Real.log (16839 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1348855783 / 1000000000) ≤ -Real.log (250000000000 / 963253582131) ∧
    -Real.log (250000000000 / 963253582131) ≤ (269771157 / 200000000) := by
  have h := checkLog_sound (w := (463253582131 / 1463253582131)) (n := 12)
    (lo := (655708603 / 1000000000)) (hi := (163927151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963253582131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(963253582131 / 500000000000) = 1/(250000000000 / 963253582131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1348855783 / 1000000000) (269771157 / 200000000) (Real.log (963253582131 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (963253582131 / 250000000000) = -Real.log (250000000000 / 963253582131) := by
    rw [show ((963253582131 / 250000000000) : ℝ) = ((250000000000 / 963253582131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1354721721 / 1000000000) ≤ -Real.log (125000000000 / 484460286349) ∧
    -Real.log (125000000000 / 484460286349) ≤ (1354721723 / 1000000000) := by
  have h := checkLog_sound (w := (234460286349 / 734460286349)) (n := 12)
    (lo := (661574541 / 1000000000)) (hi := (330787271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484460286349 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(484460286349 / 250000000000) = 1/(125000000000 / 484460286349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1354721721 / 1000000000) (1354721723 / 1000000000) (Real.log (484460286349 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (484460286349 / 125000000000) = -Real.log (125000000000 / 484460286349) := by
    rw [show ((484460286349 / 125000000000) : ℝ) = ((125000000000 / 484460286349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (992959081 / 1000000000) ≤ -Real.log (125000000000 / 337401231097) ∧
    -Real.log (125000000000 / 337401231097) ≤ (992959083 / 1000000000) := by
  have h := checkLog_sound (w := (87401231097 / 587401231097)) (n := 12)
    (lo := (299811901 / 1000000000)) (hi := (149905951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337401231097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(337401231097 / 250000000000) = 1/(125000000000 / 337401231097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (992959081 / 1000000000) (992959083 / 1000000000) (Real.log (337401231097 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (337401231097 / 125000000000) = -Real.log (125000000000 / 337401231097) := by
    rw [show ((337401231097 / 125000000000) : ℝ) = ((125000000000 / 337401231097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (249386729 / 250000000) ≤ -Real.log (250000000000 / 677905457569) ∧
    -Real.log (250000000000 / 677905457569) ≤ (498773459 / 500000000) := by
  have h := checkLog_sound (w := (177905457569 / 1177905457569)) (n := 12)
    (lo := (38049967 / 125000000)) (hi := (304399737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677905457569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(677905457569 / 500000000000) = 1/(250000000000 / 677905457569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (249386729 / 250000000) (498773459 / 500000000) (Real.log (677905457569 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (677905457569 / 250000000000) = -Real.log (250000000000 / 677905457569) := by
    rw [show ((677905457569 / 250000000000) : ℝ) = ((250000000000 / 677905457569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0095

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0096Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0096
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

theorem reflection_log_1_neg : (67350243 / 200000000) ≤ -Real.log (512 / 717) ∧
    -Real.log (512 / 717) ≤ (21046951 / 62500000) := by
  have h := checkLog_sound (w := (205 / 1229)) (n := 12)
    (lo := (67350243 / 200000000)) (hi := (21046951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 512) = 1/(512 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67350243 / 200000000) (21046951 / 62500000) (Real.log (717 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (717 / 512) = -Real.log (512 / 717) := by
    rw [show ((717 / 512) : ℝ) = ((512 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (511476877 / 1000000000) ≤ -Real.log (307 / 512) ∧
    -Real.log (307 / 512) ≤ (255738439 / 500000000) := by
  have h := checkLog_sound (w := (205 / 819)) (n := 12)
    (lo := (511476877 / 1000000000)) (hi := (255738439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 307) = 1/(307 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255738439 / 500000000) (-511476877 / 1000000000) (Real.log (307 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67182809 / 200000000) ≤ -Real.log (1280 / 1791) ∧
    -Real.log (1280 / 1791) ≤ (167957023 / 500000000) := by
  have h := checkLog_sound (w := (511 / 3071)) (n := 12)
    (lo := (67182809 / 200000000)) (hi := (167957023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1791 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1791 / 1280) = 1/(1280 / 1791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67182809 / 200000000) (167957023 / 500000000) (Real.log (1791 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1791 / 1280) = -Real.log (1280 / 1791) := by
    rw [show ((1791 / 1280) : ℝ) = ((1280 / 1791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (509524387 / 1000000000) ≤ -Real.log (769 / 1280) ∧
    -Real.log (769 / 1280) ≤ (127381097 / 250000000) := by
  have h := checkLog_sound (w := (511 / 2049)) (n := 12)
    (lo := (509524387 / 1000000000)) (hi := (127381097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 769) = 1/(769 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127381097 / 250000000) (-509524387 / 1000000000) (Real.log (769 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (294110299 / 500000000) ≤ -Real.log (256 / 461) ∧
    -Real.log (256 / 461) ≤ (588220599 / 1000000000) := by
  have h := checkLog_sound (w := (205 / 717)) (n := 12)
    (lo := (294110299 / 500000000)) (hi := (588220599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 256) = 1/(256 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (294110299 / 500000000) (588220599 / 1000000000) (Real.log (461 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (461 / 256) = -Real.log (256 / 461) := by
    rw [show ((461 / 256) : ℝ) = ((256 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (161335181 / 100000000) ≤ -Real.log (51 / 256) ∧
    -Real.log (51 / 256) ≤ (1613351813 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 51) = 1/(51 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1613351813 / 1000000000) (-161335181 / 100000000) (Real.log (51 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73364779 / 125000000) ≤ -Real.log (640 / 1151) ∧
    -Real.log (640 / 1151) ≤ (586918233 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1791)) (n := 12)
    (lo := (73364779 / 125000000)) (hi := (586918233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 640) = 1/(640 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73364779 / 125000000) (586918233 / 1000000000) (Real.log (1151 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1151 / 640) = -Real.log (640 / 1151) := by
    rw [show ((1151 / 640) : ℝ) = ((640 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160165577 / 100000000) ≤ -Real.log (129 / 640) ∧
    -Real.log (129 / 640) ≤ (1601655773 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 129) = 1/(129 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1601655773 / 1000000000) (-160165577 / 100000000) (Real.log (129 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (461198729 / 1000000000) ≤ -Real.log (500000 / 792987) ∧
    -Real.log (500000 / 792987) ≤ (46119873 / 100000000) := by
  have h := checkLog_sound (w := (292987 / 1292987)) (n := 12)
    (lo := (461198729 / 1000000000)) (hi := (46119873 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792987 / 500000) = 1/(500000 / 792987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (461198729 / 1000000000) (46119873 / 100000000) (Real.log (792987 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (792987 / 500000) = -Real.log (500000 / 792987) := by
    rw [show ((792987 / 500000) : ℝ) = ((500000 / 792987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (110228313 / 125000000) ≤ -Real.log (207013 / 500000) ∧
    -Real.log (207013 / 500000) ≤ (440913253 / 500000000) := by
  have h := checkLog_sound (w := (42987 / 457013)) (n := 12)
    (lo := (47169831 / 250000000)) (hi := (7547173 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207013) = 1/(207013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-440913253 / 500000000) (-110228313 / 125000000) (Real.log (207013 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (462403571 / 1000000000) ≤ -Real.log (500000 / 793943) ∧
    -Real.log (500000 / 793943) ≤ (115600893 / 250000000) := by
  have h := checkLog_sound (w := (293943 / 1293943)) (n := 12)
    (lo := (462403571 / 1000000000)) (hi := (115600893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793943 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793943 / 500000) = 1/(500000 / 793943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (462403571 / 1000000000) (115600893 / 250000000) (Real.log (793943 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (793943 / 500000) = -Real.log (500000 / 793943) := by
    rw [show ((793943 / 500000) : ℝ) = ((500000 / 793943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (221613817 / 250000000) ≤ -Real.log (206057 / 500000) ∧
    -Real.log (206057 / 500000) ≤ (88645527 / 100000000) := by
  have h := checkLog_sound (w := (43943 / 456057)) (n := 12)
    (lo := (24163511 / 125000000)) (hi := (193308089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206057) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 206057) = 1/(206057 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88645527 / 100000000) (-221613817 / 250000000) (Real.log (206057 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (376752141 / 1000000000) ≤ -Real.log (1000000 / 1457543) ∧
    -Real.log (1000000 / 1457543) ≤ (188376071 / 500000000) := by
  have h := checkLog_sound (w := (457543 / 2457543)) (n := 12)
    (lo := (376752141 / 1000000000)) (hi := (188376071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457543 / 1000000) = 1/(1000000 / 1457543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (376752141 / 1000000000) (188376071 / 500000000) (Real.log (1457543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1457543 / 1000000) = -Real.log (1000000 / 1457543) := by
    rw [show ((1457543 / 1000000) : ℝ) = ((1000000 / 1457543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (611646459 / 1000000000) ≤ -Real.log (542457 / 1000000) ∧
    -Real.log (542457 / 1000000) ≤ (30582323 / 50000000) := by
  have h := checkLog_sound (w := (457543 / 1542457)) (n := 12)
    (lo := (611646459 / 1000000000)) (hi := (30582323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 542457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 542457) = 1/(542457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-30582323 / 50000000) (-611646459 / 1000000000) (Real.log (542457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47248463 / 125000000) ≤ -Real.log (200000 / 291869) ∧
    -Real.log (200000 / 291869) ≤ (75597541 / 200000000) := by
  have h := checkLog_sound (w := (91869 / 491869)) (n := 12)
    (lo := (47248463 / 125000000)) (hi := (75597541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291869 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291869 / 200000) = 1/(200000 / 291869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47248463 / 125000000) (75597541 / 200000000) (Real.log (291869 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (291869 / 200000) = -Real.log (200000 / 291869) := by
    rw [show ((291869 / 200000) : ℝ) = ((200000 / 291869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (614973911 / 1000000000) ≤ -Real.log (108131 / 200000) ∧
    -Real.log (108131 / 200000) ≤ (76871739 / 125000000) := by
  have h := checkLog_sound (w := (91869 / 308131)) (n := 12)
    (lo := (614973911 / 1000000000)) (hi := (76871739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 108131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 108131) = 1/(108131 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-76871739 / 125000000) (-614973911 / 1000000000) (Real.log (108131 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (671512617 / 500000000) ≤ -Real.log (100000000000 / 383061450247) ∧
    -Real.log (100000000000 / 383061450247) ≤ (335756309 / 250000000) := by
  have h := checkLog_sound (w := (183061450247 / 583061450247)) (n := 12)
    (lo := (324939027 / 500000000)) (hi := (129975611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383061450247 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383061450247 / 200000000000) = 1/(100000000000 / 383061450247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (671512617 / 500000000) (335756309 / 250000000) (Real.log (383061450247 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (383061450247 / 100000000000) = -Real.log (100000000000 / 383061450247) := by
    rw [show ((383061450247 / 100000000000) : ℝ) = ((100000000000 / 383061450247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33721471 / 25000000) ≤ -Real.log (250000000000 / 963256526107) ∧
    -Real.log (250000000000 / 963256526107) ≤ (674429421 / 500000000) := by
  have h := checkLog_sound (w := (463256526107 / 1463256526107)) (n := 12)
    (lo := (32785583 / 50000000)) (hi := (655711661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963256526107 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(963256526107 / 500000000000) = 1/(250000000000 / 963256526107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33721471 / 25000000) (674429421 / 500000000) (Real.log (963256526107 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (963256526107 / 250000000000) = -Real.log (250000000000 / 963256526107) := by
    rw [show ((963256526107 / 250000000000) : ℝ) = ((250000000000 / 963256526107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4941993 / 5000000) ≤ -Real.log (500000000000 / 1343464090241) ∧
    -Real.log (500000000000 / 1343464090241) ≤ (494199301 / 500000000) := by
  have h := checkLog_sound (w := (343464090241 / 2343464090241)) (n := 12)
    (lo := (14762571 / 50000000)) (hi := (295251421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343464090241 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1343464090241 / 1000000000000) = 1/(500000000000 / 1343464090241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4941993 / 5000000) (494199301 / 500000000) (Real.log (1343464090241 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1343464090241 / 500000000000) = -Real.log (500000000000 / 1343464090241) := by
    rw [show ((1343464090241 / 500000000000) : ℝ) = ((500000000000 / 1343464090241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (198592323 / 200000000) ≤ -Real.log (500000000000 / 1349608345433) ∧
    -Real.log (500000000000 / 1349608345433) ≤ (992961617 / 1000000000) := by
  have h := checkLog_sound (w := (349608345433 / 2349608345433)) (n := 12)
    (lo := (59962887 / 200000000)) (hi := (74953609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349608345433 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1349608345433 / 1000000000000) = 1/(500000000000 / 1349608345433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (198592323 / 200000000) (992961617 / 1000000000) (Real.log (1349608345433 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1349608345433 / 500000000000) = -Real.log (500000000000 / 1349608345433) := by
    rw [show ((1349608345433 / 500000000000) : ℝ) = ((500000000000 / 1349608345433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0096

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0097Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0097
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

theorem reflection_log_1_neg : (67182809 / 200000000) ≤ -Real.log (1280 / 1791) ∧
    -Real.log (1280 / 1791) ≤ (167957023 / 500000000) := by
  have h := checkLog_sound (w := (511 / 3071)) (n := 12)
    (lo := (67182809 / 200000000)) (hi := (167957023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1791 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1791 / 1280) = 1/(1280 / 1791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67182809 / 200000000) (167957023 / 500000000) (Real.log (1791 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1791 / 1280) = -Real.log (1280 / 1791) := by
    rw [show ((1791 / 1280) : ℝ) = ((1280 / 1791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (509524387 / 1000000000) ≤ -Real.log (769 / 1280) ∧
    -Real.log (769 / 1280) ≤ (127381097 / 250000000) := by
  have h := checkLog_sound (w := (511 / 2049)) (n := 12)
    (lo := (509524387 / 1000000000)) (hi := (127381097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 769) = 1/(769 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127381097 / 250000000) (-509524387 / 1000000000) (Real.log (769 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335076173 / 1000000000) ≤ -Real.log (2560 / 3579) ∧
    -Real.log (2560 / 3579) ≤ (167538087 / 500000000) := by
  have h := checkLog_sound (w := (1019 / 6139)) (n := 12)
    (lo := (335076173 / 1000000000)) (hi := (167538087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3579 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3579 / 2560) = 1/(2560 / 3579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335076173 / 1000000000) (167538087 / 500000000) (Real.log (3579 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3579 / 2560) = -Real.log (2560 / 3579) := by
    rw [show ((3579 / 2560) : ℝ) = ((2560 / 3579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (253787851 / 500000000) ≤ -Real.log (1541 / 2560) ∧
    -Real.log (1541 / 2560) ≤ (507575703 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 4101)) (n := 12)
    (lo := (253787851 / 500000000)) (hi := (507575703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1541) = 1/(1541 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-507575703 / 1000000000) (-253787851 / 500000000) (Real.log (1541 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73364779 / 125000000) ≤ -Real.log (640 / 1151) ∧
    -Real.log (640 / 1151) ≤ (586918233 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1791)) (n := 12)
    (lo := (73364779 / 125000000)) (hi := (586918233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 640) = 1/(640 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73364779 / 125000000) (586918233 / 1000000000) (Real.log (1151 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1151 / 640) = -Real.log (640 / 1151) := by
    rw [show ((1151 / 640) : ℝ) = ((640 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (160165577 / 100000000) ≤ -Real.log (129 / 640) ∧
    -Real.log (129 / 640) ≤ (1601655773 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 129) = 1/(129 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1601655773 / 1000000000) (-160165577 / 100000000) (Real.log (129 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (585614167 / 1000000000) ≤ -Real.log (1280 / 2299) ∧
    -Real.log (1280 / 2299) ≤ (73201771 / 125000000) := by
  have h := checkLog_sound (w := (1019 / 3579)) (n := 12)
    (lo := (585614167 / 1000000000)) (hi := (73201771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2299 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2299 / 1280) = 1/(1280 / 2299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (585614167 / 1000000000) (73201771 / 125000000) (Real.log (2299 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2299 / 1280) = -Real.log (1280 / 2299) := by
    rw [show ((2299 / 1280) : ℝ) = ((1280 / 2299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (397523737 / 250000000) ≤ -Real.log (261 / 1280) ∧
    -Real.log (261 / 1280) ≤ (1590094951 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 261) = 1/(261 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1590094951 / 1000000000) (-397523737 / 250000000) (Real.log (261 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (459994959 / 1000000000) ≤ -Real.log (500000 / 792033) ∧
    -Real.log (500000 / 792033) ≤ (5749937 / 12500000) := by
  have h := checkLog_sound (w := (292033 / 1292033)) (n := 12)
    (lo := (459994959 / 1000000000)) (hi := (5749937 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792033 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792033 / 500000) = 1/(500000 / 792033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (459994959 / 1000000000) (5749937 / 12500000) (Real.log (792033 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (792033 / 500000) = -Real.log (500000 / 792033) := by
    rw [show ((792033 / 500000) : ℝ) = ((500000 / 792033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219307171 / 250000000) ≤ -Real.log (207967 / 500000) ∧
    -Real.log (207967 / 500000) ≤ (438614343 / 500000000) := by
  have h := checkLog_sound (w := (42033 / 457967)) (n := 12)
    (lo := (5752547 / 31250000)) (hi := (36816301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207967) = 1/(207967 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-438614343 / 500000000) (-219307171 / 250000000) (Real.log (207967 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180156 / 390625) ≤ -Real.log (40000 / 63439) ∧
    -Real.log (40000 / 63439) ≤ (461199361 / 1000000000) := by
  have h := checkLog_sound (w := (23439 / 103439)) (n := 12)
    (lo := (180156 / 390625)) (hi := (461199361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63439 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63439 / 40000) = 1/(40000 / 63439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180156 / 390625) (461199361 / 1000000000) (Real.log (63439 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (63439 / 40000) = -Real.log (40000 / 63439) := by
    rw [show ((63439 / 40000) : ℝ) = ((40000 / 63439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (881828919 / 1000000000) ≤ -Real.log (16561 / 40000) ∧
    -Real.log (16561 / 40000) ≤ (881828921 / 1000000000) := by
  have h := checkLog_sound (w := (3439 / 36561)) (n := 12)
    (lo := (188681739 / 1000000000)) (hi := (9434087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 16561) = 1/(16561 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-881828921 / 1000000000) (-881828919 / 1000000000) (Real.log (16561 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (375519857 / 1000000000) ≤ -Real.log (250000 / 363937) ∧
    -Real.log (250000 / 363937) ≤ (187759929 / 500000000) := by
  have h := checkLog_sound (w := (113937 / 613937)) (n := 12)
    (lo := (375519857 / 1000000000)) (hi := (187759929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363937 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363937 / 250000) = 1/(250000 / 363937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (375519857 / 1000000000) (187759929 / 500000000) (Real.log (363937 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (363937 / 250000) = -Real.log (250000 / 363937) := by
    rw [show ((363937 / 250000) : ℝ) = ((250000 / 363937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76042863 / 125000000) ≤ -Real.log (136063 / 250000) ∧
    -Real.log (136063 / 250000) ≤ (121668581 / 200000000) := by
  have h := checkLog_sound (w := (113937 / 386063)) (n := 12)
    (lo := (76042863 / 125000000)) (hi := (121668581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 136063) = 1/(136063 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121668581 / 200000000) (-76042863 / 125000000) (Real.log (136063 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (376752827 / 1000000000) ≤ -Real.log (125000 / 182193) ∧
    -Real.log (125000 / 182193) ≤ (94188207 / 250000000) := by
  have h := checkLog_sound (w := (57193 / 307193)) (n := 12)
    (lo := (376752827 / 1000000000)) (hi := (94188207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182193 / 125000) = 1/(125000 / 182193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (376752827 / 1000000000) (94188207 / 250000000) (Real.log (182193 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (182193 / 125000) = -Real.log (125000 / 182193) := by
    rw [show ((182193 / 125000) : ℝ) = ((125000 / 182193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (305824151 / 500000000) ≤ -Real.log (67807 / 125000) ∧
    -Real.log (67807 / 125000) ≤ (611648303 / 1000000000) := by
  have h := checkLog_sound (w := (57193 / 192807)) (n := 12)
    (lo := (305824151 / 500000000)) (hi := (611648303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67807) = 1/(67807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-611648303 / 1000000000) (-305824151 / 500000000) (Real.log (67807 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1337223643 / 1000000000) ≤ -Real.log (2500000000 / 9521137969) ∧
    -Real.log (2500000000 / 9521137969) ≤ (267444729 / 200000000) := by
  have h := checkLog_sound (w := (4521137969 / 14521137969)) (n := 12)
    (lo := (644076463 / 1000000000)) (hi := (40254779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9521137969 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9521137969 / 5000000000) = 1/(2500000000 / 9521137969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1337223643 / 1000000000) (267444729 / 200000000) (Real.log (9521137969 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9521137969 / 2500000000) = -Real.log (2500000000 / 9521137969) := by
    rw [show ((9521137969 / 2500000000) : ℝ) = ((2500000000 / 9521137969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33575707 / 25000000) ≤ -Real.log (500000000000 / 1915313084959) ∧
    -Real.log (500000000000 / 1915313084959) ≤ (671514141 / 500000000) := by
  have h := checkLog_sound (w := (915313084959 / 2915313084959)) (n := 12)
    (lo := (6498811 / 10000000)) (hi := (649881101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1915313084959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1915313084959 / 1000000000000) = 1/(500000000000 / 1915313084959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33575707 / 25000000) (671514141 / 500000000) (Real.log (1915313084959 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1915313084959 / 500000000000) = -Real.log (500000000000 / 1915313084959) := by
    rw [show ((1915313084959 / 500000000000) : ℝ) = ((500000000000 / 1915313084959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (983862761 / 1000000000) ≤ -Real.log (500000000000 / 1337384152929) ∧
    -Real.log (500000000000 / 1337384152929) ≤ (983862763 / 1000000000) := by
  have h := checkLog_sound (w := (337384152929 / 2337384152929)) (n := 12)
    (lo := (290715581 / 1000000000)) (hi := (145357791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337384152929 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1337384152929 / 1000000000000) = 1/(500000000000 / 1337384152929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (983862761 / 1000000000) (983862763 / 1000000000) (Real.log (1337384152929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1337384152929 / 500000000000) = -Real.log (500000000000 / 1337384152929) := by
    rw [show ((1337384152929 / 500000000000) : ℝ) = ((500000000000 / 1337384152929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (988401129 / 1000000000) ≤ -Real.log (15625000000 / 41983359019) ∧
    -Real.log (15625000000 / 41983359019) ≤ (988401131 / 1000000000) := by
  have h := checkLog_sound (w := (10733359019 / 73233359019)) (n := 12)
    (lo := (295253949 / 1000000000)) (hi := (5905079 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41983359019 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(41983359019 / 31250000000) = 1/(15625000000 / 41983359019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (988401129 / 1000000000) (988401131 / 1000000000) (Real.log (41983359019 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (41983359019 / 15625000000) = -Real.log (15625000000 / 41983359019) := by
    rw [show ((41983359019 / 15625000000) : ℝ) = ((15625000000 / 41983359019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0097

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0098Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0098
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

theorem reflection_log_1_neg : (335076173 / 1000000000) ≤ -Real.log (2560 / 3579) ∧
    -Real.log (2560 / 3579) ≤ (167538087 / 500000000) := by
  have h := checkLog_sound (w := (1019 / 6139)) (n := 12)
    (lo := (335076173 / 1000000000)) (hi := (167538087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3579 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3579 / 2560) = 1/(2560 / 3579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335076173 / 1000000000) (167538087 / 500000000) (Real.log (3579 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3579 / 2560) = -Real.log (2560 / 3579) := by
    rw [show ((3579 / 2560) : ℝ) = ((2560 / 3579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (253787851 / 500000000) ≤ -Real.log (1541 / 2560) ∧
    -Real.log (1541 / 2560) ≤ (507575703 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 4101)) (n := 12)
    (lo := (253787851 / 500000000)) (hi := (507575703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1541) = 1/(1541 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-507575703 / 1000000000) (-253787851 / 500000000) (Real.log (1541 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167118799 / 500000000) ≤ -Real.log (320 / 447) ∧
    -Real.log (320 / 447) ≤ (334237599 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 767)) (n := 12)
    (lo := (167118799 / 500000000)) (hi := (334237599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447 / 320) = 1/(320 / 447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167118799 / 500000000) (334237599 / 1000000000) (Real.log (447 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (447 / 320) = -Real.log (320 / 447) := by
    rw [show ((447 / 320) : ℝ) = ((320 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252815403 / 500000000) ≤ -Real.log (193 / 320) ∧
    -Real.log (193 / 320) ≤ (505630807 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 513)) (n := 12)
    (lo := (252815403 / 500000000)) (hi := (505630807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 193) = 1/(193 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-505630807 / 1000000000) (-252815403 / 500000000) (Real.log (193 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (585614167 / 1000000000) ≤ -Real.log (1280 / 2299) ∧
    -Real.log (1280 / 2299) ≤ (73201771 / 125000000) := by
  have h := checkLog_sound (w := (1019 / 3579)) (n := 12)
    (lo := (585614167 / 1000000000)) (hi := (73201771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2299 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2299 / 1280) = 1/(1280 / 2299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (585614167 / 1000000000) (73201771 / 125000000) (Real.log (2299 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2299 / 1280) = -Real.log (1280 / 2299) := by
    rw [show ((2299 / 1280) : ℝ) = ((1280 / 2299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (397523737 / 250000000) ≤ -Real.log (261 / 1280) ∧
    -Real.log (261 / 1280) ≤ (1590094951 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 261) = 1/(261 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1590094951 / 1000000000) (-397523737 / 250000000) (Real.log (261 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (229395817 / 500000000) ≤ -Real.log (1000000 / 1582161) ∧
    -Real.log (1000000 / 1582161) ≤ (91758327 / 200000000) := by
  have h := checkLog_sound (w := (582161 / 2582161)) (n := 12)
    (lo := (229395817 / 500000000)) (hi := (91758327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1582161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1582161 / 1000000) = 1/(1000000 / 1582161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (229395817 / 500000000) (91758327 / 200000000) (Real.log (1582161 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1582161 / 1000000) = -Real.log (1000000 / 1582161) := by
    rw [show ((1582161 / 1000000) : ℝ) = ((1000000 / 1582161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (872659087 / 1000000000) ≤ -Real.log (417839 / 1000000) ∧
    -Real.log (417839 / 1000000) ≤ (872659089 / 1000000000) := by
  have h := checkLog_sound (w := (82161 / 917839)) (n := 12)
    (lo := (179511907 / 1000000000)) (hi := (44877977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 417839) = 1/(417839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-872659089 / 1000000000) (-872659087 / 1000000000) (Real.log (417839 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45999559 / 100000000) ≤ -Real.log (1000000 / 1584067) ∧
    -Real.log (1000000 / 1584067) ≤ (459995591 / 1000000000) := by
  have h := checkLog_sound (w := (584067 / 2584067)) (n := 12)
    (lo := (45999559 / 100000000)) (hi := (459995591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1584067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1584067 / 1000000) = 1/(1000000 / 1584067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45999559 / 100000000) (459995591 / 1000000000) (Real.log (1584067 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1584067 / 1000000) = -Real.log (1000000 / 1584067) := by
    rw [show ((1584067 / 1000000) : ℝ) = ((1000000 / 1584067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (54826943 / 62500000) ≤ -Real.log (415933 / 1000000) ∧
    -Real.log (415933 / 1000000) ≤ (87723109 / 100000000) := by
  have h := checkLog_sound (w := (84067 / 915933)) (n := 12)
    (lo := (46020977 / 250000000)) (hi := (184083909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 415933) = 1/(415933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87723109 / 100000000) (-54826943 / 62500000) (Real.log (415933 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (18714509 / 50000000) ≤ -Real.log (1000000 / 1453959) ∧
    -Real.log (1000000 / 1453959) ≤ (374290181 / 1000000000) := by
  have h := checkLog_sound (w := (453959 / 2453959)) (n := 12)
    (lo := (18714509 / 50000000)) (hi := (374290181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453959 / 1000000) = 1/(1000000 / 1453959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (18714509 / 50000000) (374290181 / 1000000000) (Real.log (1453959 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1453959 / 1000000) = -Real.log (1000000 / 1453959) := by
    rw [show ((1453959 / 1000000) : ℝ) = ((1000000 / 1453959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (302530607 / 500000000) ≤ -Real.log (546041 / 1000000) ∧
    -Real.log (546041 / 1000000) ≤ (121012243 / 200000000) := by
  have h := checkLog_sound (w := (453959 / 1546041)) (n := 12)
    (lo := (302530607 / 500000000)) (hi := (121012243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 546041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 546041) = 1/(546041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121012243 / 200000000) (-302530607 / 500000000) (Real.log (546041 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11735017 / 31250000) ≤ -Real.log (1000000 / 1455749) ∧
    -Real.log (1000000 / 1455749) ≤ (75104109 / 200000000) := by
  have h := checkLog_sound (w := (455749 / 2455749)) (n := 12)
    (lo := (11735017 / 31250000)) (hi := (75104109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455749 / 1000000) = 1/(1000000 / 1455749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11735017 / 31250000) (75104109 / 200000000) (Real.log (1455749 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1455749 / 1000000) = -Real.log (1000000 / 1455749) := by
    rw [show ((1455749 / 1000000) : ℝ) = ((1000000 / 1455749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (608344741 / 1000000000) ≤ -Real.log (544251 / 1000000) ∧
    -Real.log (544251 / 1000000) ≤ (304172371 / 500000000) := by
  have h := checkLog_sound (w := (455749 / 1544251)) (n := 12)
    (lo := (608344741 / 1000000000)) (hi := (304172371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544251) = 1/(544251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-304172371 / 500000000) (-608344741 / 1000000000) (Real.log (544251 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1331450721 / 1000000000) ≤ -Real.log (500000000000 / 1893266305921) ∧
    -Real.log (500000000000 / 1893266305921) ≤ (1331450723 / 1000000000) := by
  have h := checkLog_sound (w := (893266305921 / 2893266305921)) (n := 12)
    (lo := (638303541 / 1000000000)) (hi := (319151771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893266305921 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1893266305921 / 1000000000000) = 1/(500000000000 / 1893266305921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1331450721 / 1000000000) (1331450723 / 1000000000) (Real.log (1893266305921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1893266305921 / 500000000000) = -Real.log (500000000000 / 1893266305921) := by
    rw [show ((1893266305921 / 500000000000) : ℝ) = ((500000000000 / 1893266305921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1337226679 / 1000000000) ≤ -Real.log (250000000000 / 952116687063) ∧
    -Real.log (250000000000 / 952116687063) ≤ (1337226681 / 1000000000) := by
  have h := checkLog_sound (w := (452116687063 / 1452116687063)) (n := 12)
    (lo := (644079499 / 1000000000)) (hi := (1288159 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((952116687063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(952116687063 / 500000000000) = 1/(250000000000 / 952116687063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1337226679 / 1000000000) (1337226681 / 1000000000) (Real.log (952116687063 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (952116687063 / 250000000000) = -Real.log (250000000000 / 952116687063) := by
    rw [show ((952116687063 / 250000000000) : ℝ) = ((250000000000 / 952116687063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (489675697 / 500000000) ≤ -Real.log (500000000000 / 1331364311471) ∧
    -Real.log (500000000000 / 1331364311471) ≤ (244837849 / 250000000) := by
  have h := checkLog_sound (w := (331364311471 / 2331364311471)) (n := 12)
    (lo := (143102107 / 500000000)) (hi := (57240843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331364311471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331364311471 / 1000000000000) = 1/(500000000000 / 1331364311471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (489675697 / 500000000) (244837849 / 250000000) (Real.log (1331364311471 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1331364311471 / 500000000000) = -Real.log (500000000000 / 1331364311471) := by
    rw [show ((1331364311471 / 500000000000) : ℝ) = ((500000000000 / 1331364311471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (196773057 / 200000000) ≤ -Real.log (125000000000 / 334346882229) ∧
    -Real.log (125000000000 / 334346882229) ≤ (983865287 / 1000000000) := by
  have h := checkLog_sound (w := (84346882229 / 584346882229)) (n := 12)
    (lo := (58143621 / 200000000)) (hi := (145359053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334346882229 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(334346882229 / 250000000000) = 1/(125000000000 / 334346882229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (196773057 / 200000000) (983865287 / 1000000000) (Real.log (334346882229 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (334346882229 / 125000000000) = -Real.log (125000000000 / 334346882229) := by
    rw [show ((334346882229 / 125000000000) : ℝ) = ((125000000000 / 334346882229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0098

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0099Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0099
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

theorem reflection_log_1_neg : (167118799 / 500000000) ≤ -Real.log (320 / 447) ∧
    -Real.log (320 / 447) ≤ (334237599 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 767)) (n := 12)
    (lo := (167118799 / 500000000)) (hi := (334237599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447 / 320) = 1/(320 / 447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (167118799 / 500000000) (334237599 / 1000000000) (Real.log (447 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (447 / 320) = -Real.log (320 / 447) := by
    rw [show ((447 / 320) : ℝ) = ((320 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252815403 / 500000000) ≤ -Real.log (193 / 320) ∧
    -Real.log (193 / 320) ≤ (505630807 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 513)) (n := 12)
    (lo := (252815403 / 500000000)) (hi := (505630807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 193) = 1/(193 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-505630807 / 1000000000) (-252815403 / 500000000) (Real.log (193 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4167479 / 12500000) ≤ -Real.log (2560 / 3573) ∧
    -Real.log (2560 / 3573) ≤ (333398321 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 6133)) (n := 12)
    (lo := (4167479 / 12500000)) (hi := (333398321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3573 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3573 / 2560) = 1/(2560 / 3573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4167479 / 12500000) (333398321 / 1000000000) (Real.log (3573 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3573 / 2560) = -Real.log (2560 / 3573) := by
    rw [show ((3573 / 2560) : ℝ) = ((2560 / 3573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251844843 / 500000000) ≤ -Real.log (1547 / 2560) ∧
    -Real.log (1547 / 2560) ≤ (503689687 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 4107)) (n := 12)
    (lo := (251844843 / 500000000)) (hi := (503689687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1547) = 1/(1547 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-503689687 / 1000000000) (-251844843 / 500000000) (Real.log (1547 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23320037 / 40000000) ≤ -Real.log (1280 / 2293) ∧
    -Real.log (1280 / 2293) ≤ (291500463 / 500000000) := by
  have h := checkLog_sound (w := (1013 / 3573)) (n := 12)
    (lo := (23320037 / 40000000)) (hi := (291500463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2293 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2293 / 1280) = 1/(1280 / 2293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23320037 / 40000000) (291500463 / 500000000) (Real.log (2293 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2293 / 1280) = -Real.log (1280 / 2293) := by
    rw [show ((2293 / 1280) : ℝ) = ((1280 / 2293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1567366697 / 1000000000) ≤ -Real.log (267 / 1280) ∧
    -Real.log (267 / 1280) ≤ (15673667 / 10000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 267) = 1/(267 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15673667 / 10000000) (-1567366697 / 1000000000) (Real.log (267 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (457588757 / 1000000000) ≤ -Real.log (1000000 / 1580259) ∧
    -Real.log (1000000 / 1580259) ≤ (228794379 / 500000000) := by
  have h := checkLog_sound (w := (580259 / 2580259)) (n := 12)
    (lo := (457588757 / 1000000000)) (hi := (228794379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1580259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1580259 / 1000000) = 1/(1000000 / 1580259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (457588757 / 1000000000) (228794379 / 500000000) (Real.log (1580259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1580259 / 1000000) = -Real.log (1000000 / 1580259) := by
    rw [show ((1580259 / 1000000) : ℝ) = ((1000000 / 1580259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54257339 / 62500000) ≤ -Real.log (419741 / 1000000) ∧
    -Real.log (419741 / 1000000) ≤ (434058713 / 500000000) := by
  have h := checkLog_sound (w := (80259 / 919741)) (n := 12)
    (lo := (43742561 / 250000000)) (hi := (34994049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419741) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 419741) = 1/(419741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-434058713 / 500000000) (-54257339 / 62500000) (Real.log (419741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (229396133 / 500000000) ≤ -Real.log (500000 / 791081) ∧
    -Real.log (500000 / 791081) ≤ (458792267 / 1000000000) := by
  have h := checkLog_sound (w := (291081 / 1291081)) (n := 12)
    (lo := (229396133 / 500000000)) (hi := (458792267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791081 / 500000) = 1/(500000 / 791081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (229396133 / 500000000) (458792267 / 1000000000) (Real.log (791081 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (791081 / 500000) = -Real.log (500000 / 791081) := by
    rw [show ((791081 / 500000) : ℝ) = ((500000 / 791081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21816537 / 25000000) ≤ -Real.log (208919 / 500000) ∧
    -Real.log (208919 / 500000) ≤ (436330741 / 500000000) := by
  have h := checkLog_sound (w := (41081 / 458919)) (n := 12)
    (lo := (1795143 / 10000000)) (hi := (179514301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208919) = 1/(208919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-436330741 / 500000000) (-21816537 / 25000000) (Real.log (208919 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (373063121 / 1000000000) ≤ -Real.log (62500 / 90761) ∧
    -Real.log (62500 / 90761) ≤ (186531561 / 500000000) := by
  have h := checkLog_sound (w := (28261 / 153261)) (n := 12)
    (lo := (373063121 / 1000000000)) (hi := (186531561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90761 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90761 / 62500) = 1/(62500 / 90761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (373063121 / 1000000000) (186531561 / 500000000) (Real.log (90761 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90761 / 62500) = -Real.log (62500 / 90761) := by
    rw [show ((90761 / 62500) : ℝ) = ((62500 / 90761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601801211 / 1000000000) ≤ -Real.log (34239 / 62500) ∧
    -Real.log (34239 / 62500) ≤ (150450303 / 250000000) := by
  have h := checkLog_sound (w := (28261 / 96739)) (n := 12)
    (lo := (601801211 / 1000000000)) (hi := (150450303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34239) = 1/(34239 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-150450303 / 250000000) (-601801211 / 1000000000) (Real.log (34239 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (93572717 / 250000000) ≤ -Real.log (25000 / 36349) ∧
    -Real.log (25000 / 36349) ≤ (374290869 / 1000000000) := by
  have h := checkLog_sound (w := (11349 / 61349)) (n := 12)
    (lo := (93572717 / 250000000)) (hi := (374290869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36349 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36349 / 25000) = 1/(25000 / 36349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93572717 / 250000000) (374290869 / 1000000000) (Real.log (36349 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (36349 / 25000) = -Real.log (25000 / 36349) := by
    rw [show ((36349 / 25000) : ℝ) = ((25000 / 36349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121012609 / 200000000) ≤ -Real.log (13651 / 25000) ∧
    -Real.log (13651 / 25000) ≤ (302531523 / 500000000) := by
  have h := checkLog_sound (w := (11349 / 38651)) (n := 12)
    (lo := (121012609 / 200000000)) (hi := (302531523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13651) = 1/(13651 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-302531523 / 500000000) (-121012609 / 200000000) (Real.log (13651 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1325706181 / 1000000000) ≤ -Real.log (250000000000 / 941210770451) ∧
    -Real.log (250000000000 / 941210770451) ≤ (1325706183 / 1000000000) := by
  have h := checkLog_sound (w := (441210770451 / 1441210770451)) (n := 12)
    (lo := (632559001 / 1000000000)) (hi := (316279501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941210770451 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(941210770451 / 500000000000) = 1/(250000000000 / 941210770451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1325706181 / 1000000000) (1325706183 / 1000000000) (Real.log (941210770451 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (941210770451 / 250000000000) = -Real.log (250000000000 / 941210770451) := by
    rw [show ((941210770451 / 250000000000) : ℝ) = ((250000000000 / 941210770451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (665726873 / 500000000) ≤ -Real.log (500000000000 / 1893272033659) ∧
    -Real.log (500000000000 / 1893272033659) ≤ (332863437 / 250000000) := by
  have h := checkLog_sound (w := (893272033659 / 2893272033659)) (n := 12)
    (lo := (319153283 / 500000000)) (hi := (638306567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893272033659 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1893272033659 / 1000000000000) = 1/(500000000000 / 1893272033659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (665726873 / 500000000) (332863437 / 250000000) (Real.log (1893272033659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1893272033659 / 500000000000) = -Real.log (500000000000 / 1893272033659) := by
    rw [show ((1893272033659 / 500000000000) : ℝ) = ((500000000000 / 1893272033659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (243716083 / 250000000) ≤ -Real.log (100000000000 / 265080755863) ∧
    -Real.log (100000000000 / 265080755863) ≤ (487432167 / 500000000) := by
  have h := checkLog_sound (w := (65080755863 / 465080755863)) (n := 12)
    (lo := (8803661 / 31250000)) (hi := (281717153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265080755863 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265080755863 / 200000000000) = 1/(100000000000 / 265080755863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (243716083 / 250000000) (487432167 / 500000000) (Real.log (265080755863 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (265080755863 / 100000000000) = -Real.log (100000000000 / 265080755863) := by
    rw [show ((265080755863 / 100000000000) : ℝ) = ((100000000000 / 265080755863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (979353913 / 1000000000) ≤ -Real.log (500000000000 / 1331367665373) ∧
    -Real.log (500000000000 / 1331367665373) ≤ (195870783 / 200000000) := by
  have h := checkLog_sound (w := (331367665373 / 2331367665373)) (n := 12)
    (lo := (286206733 / 1000000000)) (hi := (143103367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331367665373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331367665373 / 1000000000000) = 1/(500000000000 / 1331367665373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (979353913 / 1000000000) (195870783 / 200000000) (Real.log (1331367665373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1331367665373 / 500000000000) = -Real.log (500000000000 / 1331367665373) := by
    rw [show ((1331367665373 / 500000000000) : ℝ) = ((500000000000 / 1331367665373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0099

end


