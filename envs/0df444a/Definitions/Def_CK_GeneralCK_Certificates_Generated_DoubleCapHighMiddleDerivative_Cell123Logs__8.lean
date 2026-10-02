-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell123Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell123Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:40:25.714337+00:00
-- url     : https://prove2.me/theorems/6fa1e636-2f2d-4915-9066-21814126f3dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell123Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell124…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell123Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell124Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell125Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell126Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell127Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell128Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell129Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell130Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell123Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell124Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell125Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell126Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell127Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell128Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell129Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell130Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell123Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell124Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell125Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell126Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell127Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell128Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell129Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell130Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell123Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell124Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell125Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell126Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell127Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell128Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell129Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell130Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell123Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell123
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

theorem reflection_log_1_neg : (11185681 / 40000000) ≤ -Real.log (1280 / 1693) ∧
    -Real.log (1280 / 1693) ≤ (139821013 / 500000000) := by
  have h := checkLog_sound (w := (413 / 2973)) (n := 12)
    (lo := (11185681 / 40000000)) (hi := (139821013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693 / 1280) = 1/(1280 / 1693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11185681 / 40000000) (139821013 / 500000000) (Real.log (1693 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1693 / 1280) = -Real.log (1280 / 1693) := by
    rw [show ((1693 / 1280) : ℝ) = ((1280 / 1693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19478819 / 50000000) ≤ -Real.log (867 / 1280) ∧
    -Real.log (867 / 1280) ≤ (389576381 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2147)) (n := 12)
    (lo := (19478819 / 50000000)) (hi := (389576381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 867) = 1/(867 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-389576381 / 1000000000) (-19478819 / 50000000) (Real.log (867 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (139599463 / 500000000) ≤ -Real.log (5120 / 6769) ∧
    -Real.log (5120 / 6769) ≤ (279198927 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 11889)) (n := 12)
    (lo := (139599463 / 500000000)) (hi := (279198927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6769 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6769 / 5120) = 1/(5120 / 6769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (139599463 / 500000000) (279198927 / 1000000000) (Real.log (6769 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6769 / 5120) = -Real.log (5120 / 6769) := by
    rw [show ((6769 / 5120) : ℝ) = ((5120 / 6769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (194355851 / 500000000) ≤ -Real.log (3471 / 5120) ∧
    -Real.log (3471 / 5120) ≤ (388711703 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 8591)) (n := 12)
    (lo := (194355851 / 500000000)) (hi := (388711703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3471) = 1/(3471 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-388711703 / 1000000000) (-194355851 / 500000000) (Real.log (3471 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (206011227 / 1000000000) ≤ -Real.log (1000000 / 1228767) ∧
    -Real.log (1000000 / 1228767) ≤ (51502807 / 250000000) := by
  have h := checkLog_sound (w := (228767 / 2228767)) (n := 12)
    (lo := (206011227 / 1000000000)) (hi := (51502807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228767 / 1000000) = 1/(1000000 / 1228767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (206011227 / 1000000000) (51502807 / 250000000) (Real.log (1228767 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1228767 / 1000000) = -Real.log (1000000 / 1228767) := by
    rw [show ((1228767 / 1000000) : ℝ) = ((1000000 / 1228767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (129882373 / 500000000) ≤ -Real.log (771233 / 1000000) ∧
    -Real.log (771233 / 1000000) ≤ (259764747 / 1000000000) := by
  have h := checkLog_sound (w := (228767 / 1771233)) (n := 12)
    (lo := (129882373 / 500000000)) (hi := (259764747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771233) = 1/(771233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259764747 / 1000000000) (-129882373 / 500000000) (Real.log (771233 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (51588447 / 250000000) ≤ -Real.log (250000 / 307297) ∧
    -Real.log (250000 / 307297) ≤ (206353789 / 1000000000) := by
  have h := checkLog_sound (w := (57297 / 557297)) (n := 12)
    (lo := (51588447 / 250000000)) (hi := (206353789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307297 / 250000) = 1/(250000 / 307297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (51588447 / 250000000) (206353789 / 1000000000) (Real.log (307297 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307297 / 250000) = -Real.log (250000 / 307297) := by
    rw [show ((307297 / 250000) : ℝ) = ((250000 / 307297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (130155387 / 500000000) ≤ -Real.log (192703 / 250000) ∧
    -Real.log (192703 / 250000) ≤ (10412431 / 40000000) := by
  have h := checkLog_sound (w := (57297 / 442703)) (n := 12)
    (lo := (130155387 / 500000000)) (hi := (10412431 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192703) = 1/(192703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10412431 / 40000000) (-130155387 / 500000000) (Real.log (192703 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151985193 / 1000000000) ≤ -Real.log (1000000 / 1164143) ∧
    -Real.log (1000000 / 1164143) ≤ (75992597 / 500000000) := by
  have h := checkLog_sound (w := (164143 / 2164143)) (n := 12)
    (lo := (151985193 / 1000000000)) (hi := (75992597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164143 / 1000000) = 1/(1000000 / 1164143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151985193 / 1000000000) (75992597 / 500000000) (Real.log (1164143 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164143 / 1000000) = -Real.log (1000000 / 1164143) := by
    rw [show ((1164143 / 1000000) : ℝ) = ((1000000 / 1164143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (179297733 / 1000000000) ≤ -Real.log (835857 / 1000000) ∧
    -Real.log (835857 / 1000000) ≤ (89648867 / 500000000) := by
  have h := checkLog_sound (w := (164143 / 1835857)) (n := 12)
    (lo := (179297733 / 1000000000)) (hi := (89648867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835857) = 1/(835857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-89648867 / 500000000) (-179297733 / 1000000000) (Real.log (835857 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152252307 / 1000000000) ≤ -Real.log (500000 / 582227) ∧
    -Real.log (500000 / 582227) ≤ (38063077 / 250000000) := by
  have h := checkLog_sound (w := (82227 / 1082227)) (n := 12)
    (lo := (152252307 / 1000000000)) (hi := (38063077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582227 / 500000) = 1/(500000 / 582227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152252307 / 1000000000) (38063077 / 250000000) (Real.log (582227 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (582227 / 500000) = -Real.log (500000 / 582227) := by
    rw [show ((582227 / 500000) : ℝ) = ((500000 / 582227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1437359 / 8000000) ≤ -Real.log (417773 / 500000) ∧
    -Real.log (417773 / 500000) ≤ (44917469 / 250000000) := by
  have h := checkLog_sound (w := (82227 / 917773)) (n := 12)
    (lo := (1437359 / 8000000)) (hi := (44917469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417773) = 1/(417773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44917469 / 250000000) (-1437359 / 8000000) (Real.log (417773 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166977657 / 250000000) ≤ -Real.log (31250000000 / 60942451743) ∧
    -Real.log (31250000000 / 60942451743) ≤ (667910629 / 1000000000) := by
  have h := checkLog_sound (w := (29692451743 / 92192451743)) (n := 12)
    (lo := (166977657 / 250000000)) (hi := (667910629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60942451743 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60942451743 / 31250000000) = 1/(31250000000 / 60942451743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166977657 / 250000000) (667910629 / 1000000000) (Real.log (60942451743 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60942451743 / 31250000000) = -Real.log (31250000000 / 60942451743) := by
    rw [show ((60942451743 / 31250000000) : ℝ) = ((31250000000 / 60942451743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133843681 / 200000000) ≤ -Real.log (250000000000 / 488177623991) ∧
    -Real.log (250000000000 / 488177623991) ≤ (334609203 / 500000000) := by
  have h := checkLog_sound (w := (238177623991 / 738177623991)) (n := 12)
    (lo := (133843681 / 200000000)) (hi := (334609203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488177623991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488177623991 / 250000000000) = 1/(250000000000 / 488177623991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (133843681 / 200000000) (334609203 / 500000000) (Real.log (488177623991 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (488177623991 / 250000000000) = -Real.log (250000000000 / 488177623991) := by
    rw [show ((488177623991 / 250000000000) : ℝ) = ((250000000000 / 488177623991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (465775973 / 1000000000) ≤ -Real.log (500000000000 / 796625014749) ∧
    -Real.log (500000000000 / 796625014749) ≤ (232887987 / 500000000) := by
  have h := checkLog_sound (w := (296625014749 / 1296625014749)) (n := 12)
    (lo := (465775973 / 1000000000)) (hi := (232887987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796625014749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796625014749 / 500000000000) = 1/(500000000000 / 796625014749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (465775973 / 1000000000) (232887987 / 500000000) (Real.log (796625014749 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (796625014749 / 500000000000) = -Real.log (500000000000 / 796625014749) := by
    rw [show ((796625014749 / 500000000000) : ℝ) = ((500000000000 / 796625014749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (466664563 / 1000000000) ≤ -Real.log (500000000000 / 797333201871) ∧
    -Real.log (500000000000 / 797333201871) ≤ (116666141 / 250000000) := by
  have h := checkLog_sound (w := (297333201871 / 1297333201871)) (n := 12)
    (lo := (466664563 / 1000000000)) (hi := (116666141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797333201871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797333201871 / 500000000000) = 1/(500000000000 / 797333201871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (466664563 / 1000000000) (116666141 / 250000000) (Real.log (797333201871 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (797333201871 / 500000000000) = -Real.log (500000000000 / 797333201871) := by
    rw [show ((797333201871 / 500000000000) : ℝ) = ((500000000000 / 797333201871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (331282927 / 1000000000) ≤ -Real.log (500000000000 / 696376892219) ∧
    -Real.log (500000000000 / 696376892219) ≤ (20705183 / 62500000) := by
  have h := checkLog_sound (w := (196376892219 / 1196376892219)) (n := 12)
    (lo := (331282927 / 1000000000)) (hi := (20705183 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696376892219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696376892219 / 500000000000) = 1/(500000000000 / 696376892219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (331282927 / 1000000000) (20705183 / 62500000) (Real.log (696376892219 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (696376892219 / 500000000000) = -Real.log (500000000000 / 696376892219) := by
    rw [show ((696376892219 / 500000000000) : ℝ) = ((500000000000 / 696376892219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (331922183 / 1000000000) ≤ -Real.log (500000000000 / 696822197701) ∧
    -Real.log (500000000000 / 696822197701) ≤ (41490273 / 125000000) := by
  have h := checkLog_sound (w := (196822197701 / 1196822197701)) (n := 12)
    (lo := (331922183 / 1000000000)) (hi := (41490273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696822197701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696822197701 / 500000000000) = 1/(500000000000 / 696822197701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (331922183 / 1000000000) (41490273 / 125000000) (Real.log (696822197701 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (696822197701 / 500000000000) = -Real.log (500000000000 / 696822197701) := by
    rw [show ((696822197701 / 500000000000) : ℝ) = ((500000000000 / 696822197701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27417567 / 1000000000) ≤ -Real.log (243238720471 / 250000000000) ∧
    -Real.log (243238720471 / 250000000000) ≤ (856799 / 31250000) := by
  have h := checkLog_sound (w := (6761279529 / 493238720471)) (n := 12)
    (lo := (27417567 / 1000000000)) (hi := (856799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243238720471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243238720471) = 1/(243238720471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-856799 / 31250000) (-27417567 / 1000000000) (Real.log (243238720471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27312539 / 1000000000) ≤ -Real.log (973057075551 / 1000000000000) ∧
    -Real.log (973057075551 / 1000000000000) ≤ (1365627 / 50000000) := by
  have h := checkLog_sound (w := (26942924449 / 1973057075551)) (n := 12)
    (lo := (27312539 / 1000000000)) (hi := (1365627 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973057075551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973057075551) = 1/(973057075551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1365627 / 50000000) (-27312539 / 1000000000) (Real.log (973057075551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell123

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell124Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell124
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

theorem reflection_log_1_neg : (280084927 / 1000000000) ≤ -Real.log (1024 / 1355) ∧
    -Real.log (1024 / 1355) ≤ (4376327 / 15625000) := by
  have h := checkLog_sound (w := (331 / 2379)) (n := 12)
    (lo := (280084927 / 1000000000)) (hi := (4376327 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355 / 1024) = 1/(1024 / 1355) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (280084927 / 1000000000) (4376327 / 15625000) (Real.log (1355 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1355 / 1024) = -Real.log (1024 / 1355) := by
    rw [show ((1355 / 1024) : ℝ) = ((1024 / 1355) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (195220903 / 500000000) ≤ -Real.log (693 / 1024) ∧
    -Real.log (693 / 1024) ≤ (390441807 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1717)) (n := 12)
    (lo := (195220903 / 500000000)) (hi := (390441807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 693) = 1/(693 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-390441807 / 1000000000) (-195220903 / 500000000) (Real.log (693 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11185681 / 40000000) ≤ -Real.log (1280 / 1693) ∧
    -Real.log (1280 / 1693) ≤ (139821013 / 500000000) := by
  have h := checkLog_sound (w := (413 / 2973)) (n := 12)
    (lo := (11185681 / 40000000)) (hi := (139821013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693 / 1280) = 1/(1280 / 1693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11185681 / 40000000) (139821013 / 500000000) (Real.log (1693 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1693 / 1280) = -Real.log (1280 / 1693) := by
    rw [show ((1693 / 1280) : ℝ) = ((1280 / 1693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19478819 / 50000000) ≤ -Real.log (867 / 1280) ∧
    -Real.log (867 / 1280) ≤ (389576381 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2147)) (n := 12)
    (lo := (19478819 / 50000000)) (hi := (389576381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 867) = 1/(867 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-389576381 / 1000000000) (-19478819 / 50000000) (Real.log (867 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8254119 / 40000000) ≤ -Real.log (1000000 / 1229187) ∧
    -Real.log (1000000 / 1229187) ≤ (12897061 / 62500000) := by
  have h := checkLog_sound (w := (229187 / 2229187)) (n := 12)
    (lo := (8254119 / 40000000)) (hi := (12897061 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229187 / 1000000) = 1/(1000000 / 1229187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8254119 / 40000000) (12897061 / 62500000) (Real.log (1229187 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229187 / 1000000) = -Real.log (1000000 / 1229187) := by
    rw [show ((1229187 / 1000000) : ℝ) = ((1000000 / 1229187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65077369 / 250000000) ≤ -Real.log (770813 / 1000000) ∧
    -Real.log (770813 / 1000000) ≤ (260309477 / 1000000000) := by
  have h := checkLog_sound (w := (229187 / 1770813)) (n := 12)
    (lo := (65077369 / 250000000)) (hi := (260309477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770813) = 1/(770813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260309477 / 1000000000) (-65077369 / 250000000) (Real.log (770813 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206695419 / 1000000000) ≤ -Real.log (125000 / 153701) ∧
    -Real.log (125000 / 153701) ≤ (10334771 / 50000000) := by
  have h := checkLog_sound (w := (28701 / 278701)) (n := 12)
    (lo := (206695419 / 1000000000)) (hi := (10334771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153701 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153701 / 125000) = 1/(125000 / 153701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206695419 / 1000000000) (10334771 / 50000000) (Real.log (153701 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153701 / 125000) = -Real.log (125000 / 153701) := by
    rw [show ((153701 / 125000) : ℝ) = ((125000 / 153701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (130427901 / 500000000) ≤ -Real.log (96299 / 125000) ∧
    -Real.log (96299 / 125000) ≤ (260855803 / 1000000000) := by
  have h := checkLog_sound (w := (28701 / 221299)) (n := 12)
    (lo := (130427901 / 500000000)) (hi := (260855803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96299) = 1/(96299 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260855803 / 1000000000) (-130427901 / 500000000) (Real.log (96299 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (19031431 / 125000000) ≤ -Real.log (1000000 / 1164453) ∧
    -Real.log (1000000 / 1164453) ≤ (152251449 / 1000000000) := by
  have h := checkLog_sound (w := (164453 / 2164453)) (n := 12)
    (lo := (19031431 / 125000000)) (hi := (152251449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164453 / 1000000) = 1/(1000000 / 1164453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (19031431 / 125000000) (152251449 / 1000000000) (Real.log (1164453 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164453 / 1000000) = -Real.log (1000000 / 1164453) := by
    rw [show ((1164453 / 1000000) : ℝ) = ((1000000 / 1164453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89834339 / 500000000) ≤ -Real.log (835547 / 1000000) ∧
    -Real.log (835547 / 1000000) ≤ (179668679 / 1000000000) := by
  have h := checkLog_sound (w := (164453 / 1835547)) (n := 12)
    (lo := (89834339 / 500000000)) (hi := (179668679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835547) = 1/(835547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-179668679 / 1000000000) (-89834339 / 500000000) (Real.log (835547 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152518491 / 1000000000) ≤ -Real.log (250000 / 291191) ∧
    -Real.log (250000 / 291191) ≤ (38129623 / 250000000) := by
  have h := checkLog_sound (w := (41191 / 541191)) (n := 12)
    (lo := (152518491 / 1000000000)) (hi := (38129623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291191 / 250000) = 1/(250000 / 291191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152518491 / 1000000000) (38129623 / 250000000) (Real.log (291191 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (291191 / 250000) = -Real.log (250000 / 291191) := by
    rw [show ((291191 / 250000) : ℝ) = ((250000 / 291191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (180040959 / 1000000000) ≤ -Real.log (208809 / 250000) ∧
    -Real.log (208809 / 250000) ≤ (140657 / 781250) := by
  have h := checkLog_sound (w := (41191 / 458809)) (n := 12)
    (lo := (180040959 / 1000000000)) (hi := (140657 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208809) = 1/(208809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140657 / 781250) (-180040959 / 1000000000) (Real.log (208809 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133843681 / 200000000) ≤ -Real.log (500000000000 / 976355247981) ∧
    -Real.log (500000000000 / 976355247981) ≤ (334609203 / 500000000) := by
  have h := checkLog_sound (w := (476355247981 / 1476355247981)) (n := 12)
    (lo := (133843681 / 200000000)) (hi := (334609203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976355247981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976355247981 / 500000000000) = 1/(500000000000 / 976355247981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133843681 / 200000000) (334609203 / 500000000) (Real.log (976355247981 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (976355247981 / 500000000000) = -Real.log (500000000000 / 976355247981) := by
    rw [show ((976355247981 / 500000000000) : ℝ) = ((500000000000 / 976355247981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (335263367 / 500000000) ≤ -Real.log (250000000000 / 488816738817) ∧
    -Real.log (250000000000 / 488816738817) ≤ (134105347 / 200000000) := by
  have h := checkLog_sound (w := (238816738817 / 738816738817)) (n := 12)
    (lo := (335263367 / 500000000)) (hi := (134105347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488816738817 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488816738817 / 250000000000) = 1/(250000000000 / 488816738817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (335263367 / 500000000) (134105347 / 200000000) (Real.log (488816738817 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (488816738817 / 250000000000) = -Real.log (250000000000 / 488816738817) := by
    rw [show ((488816738817 / 250000000000) : ℝ) = ((250000000000 / 488816738817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (116665613 / 250000000) ≤ -Real.log (250000000000 / 398665759399) ∧
    -Real.log (250000000000 / 398665759399) ≤ (466662453 / 1000000000) := by
  have h := checkLog_sound (w := (148665759399 / 648665759399)) (n := 12)
    (lo := (116665613 / 250000000)) (hi := (466662453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398665759399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398665759399 / 250000000000) = 1/(250000000000 / 398665759399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116665613 / 250000000) (466662453 / 1000000000) (Real.log (398665759399 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (398665759399 / 250000000000) = -Real.log (250000000000 / 398665759399) := by
    rw [show ((398665759399 / 250000000000) : ℝ) = ((250000000000 / 398665759399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (233775611 / 500000000) ≤ -Real.log (100000000000 / 159608095619) ∧
    -Real.log (100000000000 / 159608095619) ≤ (467551223 / 1000000000) := by
  have h := checkLog_sound (w := (59608095619 / 259608095619)) (n := 12)
    (lo := (233775611 / 500000000)) (hi := (467551223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159608095619 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159608095619 / 100000000000) = 1/(100000000000 / 159608095619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (233775611 / 500000000) (467551223 / 1000000000) (Real.log (159608095619 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (159608095619 / 100000000000) = -Real.log (100000000000 / 159608095619) := by
    rw [show ((159608095619 / 100000000000) : ℝ) = ((100000000000 / 159608095619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (331920127 / 1000000000) ≤ -Real.log (500000000000 / 696820765319) ∧
    -Real.log (500000000000 / 696820765319) ≤ (1296563 / 3906250) := by
  have h := checkLog_sound (w := (196820765319 / 1196820765319)) (n := 12)
    (lo := (331920127 / 1000000000)) (hi := (1296563 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696820765319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696820765319 / 500000000000) = 1/(500000000000 / 696820765319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (331920127 / 1000000000) (1296563 / 3906250) (Real.log (696820765319 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (696820765319 / 500000000000) = -Real.log (500000000000 / 696820765319) := by
    rw [show ((696820765319 / 500000000000) : ℝ) = ((500000000000 / 696820765319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (6651189 / 20000000) ≤ -Real.log (500000000000 / 697266401353) ∧
    -Real.log (500000000000 / 697266401353) ≤ (332559451 / 1000000000) := by
  have h := checkLog_sound (w := (197266401353 / 1197266401353)) (n := 12)
    (lo := (6651189 / 20000000)) (hi := (332559451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697266401353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697266401353 / 500000000000) = 1/(500000000000 / 697266401353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (6651189 / 20000000) (332559451 / 1000000000) (Real.log (697266401353 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (697266401353 / 500000000000) = -Real.log (500000000000 / 697266401353) := by
    rw [show ((697266401353 / 500000000000) : ℝ) = ((500000000000 / 697266401353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27522467 / 1000000000) ≤ -Real.log (60803301519 / 62500000000) ∧
    -Real.log (60803301519 / 62500000000) ≤ (6880617 / 250000000) := by
  have h := checkLog_sound (w := (1696698481 / 123303301519)) (n := 12)
    (lo := (27522467 / 1000000000)) (hi := (6880617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60803301519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60803301519) = 1/(60803301519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6880617 / 250000000) (-27522467 / 1000000000) (Real.log (60803301519 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27417229 / 1000000000) ≤ -Real.log (972955210791 / 1000000000000) ∧
    -Real.log (972955210791 / 1000000000000) ≤ (2741723 / 100000000) := by
  have h := checkLog_sound (w := (27044789209 / 1972955210791)) (n := 12)
    (lo := (27417229 / 1000000000)) (hi := (2741723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972955210791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972955210791) = 1/(972955210791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2741723 / 100000000) (-27417229 / 1000000000) (Real.log (972955210791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell124

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell125Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell125
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

theorem reflection_log_1_neg : (140263817 / 500000000) ≤ -Real.log (2560 / 3389) ∧
    -Real.log (2560 / 3389) ≤ (56105527 / 200000000) := by
  have h := checkLog_sound (w := (829 / 5949)) (n := 12)
    (lo := (140263817 / 500000000)) (hi := (56105527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3389 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3389 / 2560) = 1/(2560 / 3389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140263817 / 500000000) (56105527 / 200000000) (Real.log (3389 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3389 / 2560) = -Real.log (2560 / 3389) := by
    rw [show ((3389 / 2560) : ℝ) = ((2560 / 3389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (195653991 / 500000000) ≤ -Real.log (1731 / 2560) ∧
    -Real.log (1731 / 2560) ≤ (391307983 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 4291)) (n := 12)
    (lo := (195653991 / 500000000)) (hi := (391307983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1731) = 1/(1731 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-391307983 / 1000000000) (-195653991 / 500000000) (Real.log (1731 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (280084927 / 1000000000) ≤ -Real.log (1024 / 1355) ∧
    -Real.log (1024 / 1355) ≤ (4376327 / 15625000) := by
  have h := checkLog_sound (w := (331 / 2379)) (n := 12)
    (lo := (280084927 / 1000000000)) (hi := (4376327 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355 / 1024) = 1/(1024 / 1355) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (280084927 / 1000000000) (4376327 / 15625000) (Real.log (1355 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1355 / 1024) = -Real.log (1024 / 1355) := by
    rw [show ((1355 / 1024) : ℝ) = ((1024 / 1355) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (195220903 / 500000000) ≤ -Real.log (693 / 1024) ∧
    -Real.log (693 / 1024) ≤ (390441807 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1717)) (n := 12)
    (lo := (195220903 / 500000000)) (hi := (390441807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 693) = 1/(693 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-390441807 / 1000000000) (-195220903 / 500000000) (Real.log (693 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103347303 / 500000000) ≤ -Real.log (1000000 / 1229607) ∧
    -Real.log (1000000 / 1229607) ≤ (206694607 / 1000000000) := by
  have h := checkLog_sound (w := (229607 / 2229607)) (n := 12)
    (lo := (103347303 / 500000000)) (hi := (206694607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229607 / 1000000) = 1/(1000000 / 1229607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103347303 / 500000000) (206694607 / 1000000000) (Real.log (1229607 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229607 / 1000000) = -Real.log (1000000 / 1229607) := by
    rw [show ((1229607 / 1000000) : ℝ) = ((1000000 / 1229607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (32606813 / 125000000) ≤ -Real.log (770393 / 1000000) ∧
    -Real.log (770393 / 1000000) ≤ (52170901 / 200000000) := by
  have h := checkLog_sound (w := (229607 / 1770393)) (n := 12)
    (lo := (32606813 / 125000000)) (hi := (52170901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770393) = 1/(770393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52170901 / 200000000) (-32606813 / 125000000) (Real.log (770393 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207036933 / 1000000000) ≤ -Real.log (250000 / 307507) ∧
    -Real.log (250000 / 307507) ≤ (103518467 / 500000000) := by
  have h := checkLog_sound (w := (57507 / 557507)) (n := 12)
    (lo := (207036933 / 1000000000)) (hi := (103518467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307507 / 250000) = 1/(250000 / 307507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207036933 / 1000000000) (103518467 / 500000000) (Real.log (307507 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307507 / 250000) = -Real.log (250000 / 307507) := by
    rw [show ((307507 / 250000) : ℝ) = ((250000 / 307507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (32675141 / 125000000) ≤ -Real.log (192493 / 250000) ∧
    -Real.log (192493 / 250000) ≤ (261401129 / 1000000000) := by
  have h := checkLog_sound (w := (57507 / 442493)) (n := 12)
    (lo := (32675141 / 125000000)) (hi := (261401129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192493) = 1/(192493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-261401129 / 1000000000) (-32675141 / 125000000) (Real.log (192493 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (297886 / 1953125) ≤ -Real.log (1000000 / 1164763) ∧
    -Real.log (1000000 / 1164763) ≤ (152517633 / 1000000000) := by
  have h := checkLog_sound (w := (164763 / 2164763)) (n := 12)
    (lo := (297886 / 1953125)) (hi := (152517633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164763 / 1000000) = 1/(1000000 / 1164763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (297886 / 1953125) (152517633 / 1000000000) (Real.log (1164763 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164763 / 1000000) = -Real.log (1000000 / 1164763) := by
    rw [show ((1164763 / 1000000) : ℝ) = ((1000000 / 1164763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (90019881 / 500000000) ≤ -Real.log (835237 / 1000000) ∧
    -Real.log (835237 / 1000000) ≤ (180039763 / 1000000000) := by
  have h := checkLog_sound (w := (164763 / 1835237)) (n := 12)
    (lo := (90019881 / 500000000)) (hi := (180039763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835237) = 1/(835237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180039763 / 1000000000) (-90019881 / 500000000) (Real.log (835237 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (76392731 / 500000000) ≤ -Real.log (40000 / 46603) ∧
    -Real.log (40000 / 46603) ≤ (152785463 / 1000000000) := by
  have h := checkLog_sound (w := (6603 / 86603)) (n := 12)
    (lo := (76392731 / 500000000)) (hi := (152785463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46603 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46603 / 40000) = 1/(40000 / 46603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (76392731 / 500000000) (152785463 / 1000000000) (Real.log (46603 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46603 / 40000) = -Real.log (40000 / 46603) := by
    rw [show ((46603 / 40000) : ℝ) = ((40000 / 46603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90206689 / 500000000) ≤ -Real.log (33397 / 40000) ∧
    -Real.log (33397 / 40000) ≤ (180413379 / 1000000000) := by
  have h := checkLog_sound (w := (6603 / 73397)) (n := 12)
    (lo := (90206689 / 500000000)) (hi := (180413379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33397) = 1/(33397 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180413379 / 1000000000) (-90206689 / 500000000) (Real.log (33397 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (335263367 / 500000000) ≤ -Real.log (500000000000 / 977633477633) ∧
    -Real.log (500000000000 / 977633477633) ≤ (134105347 / 200000000) := by
  have h := checkLog_sound (w := (477633477633 / 1477633477633)) (n := 12)
    (lo := (335263367 / 500000000)) (hi := (134105347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977633477633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977633477633 / 500000000000) = 1/(500000000000 / 977633477633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (335263367 / 500000000) (134105347 / 200000000) (Real.log (977633477633 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (977633477633 / 500000000000) = -Real.log (500000000000 / 977633477633) := by
    rw [show ((977633477633 / 500000000000) : ℝ) = ((500000000000 / 977633477633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20994863 / 31250000) ≤ -Real.log (500000000000 / 978913922589) ∧
    -Real.log (500000000000 / 978913922589) ≤ (671835617 / 1000000000) := by
  have h := checkLog_sound (w := (478913922589 / 1478913922589)) (n := 12)
    (lo := (20994863 / 31250000)) (hi := (671835617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978913922589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978913922589 / 500000000000) = 1/(500000000000 / 978913922589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (20994863 / 31250000) (671835617 / 1000000000) (Real.log (978913922589 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (978913922589 / 500000000000) = -Real.log (500000000000 / 978913922589) := by
    rw [show ((978913922589 / 500000000000) : ℝ) = ((500000000000 / 978913922589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (46754911 / 100000000) ≤ -Real.log (500000000000 / 798038793187) ∧
    -Real.log (500000000000 / 798038793187) ≤ (467549111 / 1000000000) := by
  have h := checkLog_sound (w := (298038793187 / 1298038793187)) (n := 12)
    (lo := (46754911 / 100000000)) (hi := (467549111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798038793187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798038793187 / 500000000000) = 1/(500000000000 / 798038793187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46754911 / 100000000) (467549111 / 1000000000) (Real.log (798038793187 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (798038793187 / 500000000000) = -Real.log (500000000000 / 798038793187) := by
    rw [show ((798038793187 / 500000000000) : ℝ) = ((500000000000 / 798038793187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (468438061 / 1000000000) ≤ -Real.log (500000000000 / 798748525921) ∧
    -Real.log (500000000000 / 798748525921) ≤ (234219031 / 500000000) := by
  have h := checkLog_sound (w := (298748525921 / 1298748525921)) (n := 12)
    (lo := (468438061 / 1000000000)) (hi := (234219031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798748525921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798748525921 / 500000000000) = 1/(500000000000 / 798748525921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (468438061 / 1000000000) (234219031 / 500000000) (Real.log (798748525921 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (798748525921 / 500000000000) = -Real.log (500000000000 / 798748525921) := by
    rw [show ((798748525921 / 500000000000) : ℝ) = ((500000000000 / 798748525921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (166278697 / 500000000) ≤ -Real.log (500000000000 / 697264967907) ∧
    -Real.log (500000000000 / 697264967907) ≤ (66511479 / 200000000) := by
  have h := checkLog_sound (w := (197264967907 / 1197264967907)) (n := 12)
    (lo := (166278697 / 500000000)) (hi := (66511479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697264967907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697264967907 / 500000000000) = 1/(500000000000 / 697264967907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166278697 / 500000000) (66511479 / 200000000) (Real.log (697264967907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (697264967907 / 500000000000) = -Real.log (500000000000 / 697264967907) := by
    rw [show ((697264967907 / 500000000000) : ℝ) = ((500000000000 / 697264967907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (333198841 / 1000000000) ≤ -Real.log (800000000 / 1116339791) ∧
    -Real.log (800000000 / 1116339791) ≤ (166599421 / 500000000) := by
  have h := checkLog_sound (w := (316339791 / 1916339791)) (n := 12)
    (lo := (333198841 / 1000000000)) (hi := (166599421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116339791 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116339791 / 800000000) = 1/(800000000 / 1116339791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (333198841 / 1000000000) (166599421 / 500000000) (Real.log (1116339791 / 800000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1116339791 / 800000000) = -Real.log (800000000 / 1116339791) := by
    rw [show ((1116339791 / 800000000) : ℝ) = ((800000000 / 1116339791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5525583 / 200000000) ≤ -Real.log (1556400391 / 1600000000) ∧
    -Real.log (1556400391 / 1600000000) ≤ (6906979 / 250000000) := by
  have h := checkLog_sound (w := (43599609 / 3156400391)) (n := 12)
    (lo := (5525583 / 200000000)) (hi := (6906979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1556400391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1556400391) = 1/(1556400391 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6906979 / 250000000) (-5525583 / 200000000) (Real.log (1556400391 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27522129 / 1000000000) ≤ -Real.log (972853153831 / 1000000000000) ∧
    -Real.log (972853153831 / 1000000000000) ≤ (2752213 / 100000000) := by
  have h := checkLog_sound (w := (27146846169 / 1972853153831)) (n := 12)
    (lo := (27522129 / 1000000000)) (hi := (2752213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972853153831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972853153831) = 1/(972853153831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2752213 / 100000000) (-27522129 / 1000000000) (Real.log (972853153831 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell125

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell126Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell126
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

theorem reflection_log_1_neg : (8780317 / 31250000) ≤ -Real.log (5120 / 6781) ∧
    -Real.log (5120 / 6781) ≤ (56194029 / 200000000) := by
  have h := checkLog_sound (w := (1661 / 11901)) (n := 12)
    (lo := (8780317 / 31250000)) (hi := (56194029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6781 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6781 / 5120) = 1/(5120 / 6781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8780317 / 31250000) (56194029 / 200000000) (Real.log (6781 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6781 / 5120) = -Real.log (5120 / 6781) := by
    rw [show ((6781 / 5120) : ℝ) = ((5120 / 6781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (392174909 / 1000000000) ≤ -Real.log (3459 / 5120) ∧
    -Real.log (3459 / 5120) ≤ (39217491 / 100000000) := by
  have h := checkLog_sound (w := (1661 / 8579)) (n := 12)
    (lo := (392174909 / 1000000000)) (hi := (39217491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3459) = 1/(3459 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-39217491 / 100000000) (-392174909 / 1000000000) (Real.log (3459 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140263817 / 500000000) ≤ -Real.log (2560 / 3389) ∧
    -Real.log (2560 / 3389) ≤ (56105527 / 200000000) := by
  have h := checkLog_sound (w := (829 / 5949)) (n := 12)
    (lo := (140263817 / 500000000)) (hi := (56105527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3389 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3389 / 2560) = 1/(2560 / 3389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140263817 / 500000000) (56105527 / 200000000) (Real.log (3389 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3389 / 2560) = -Real.log (2560 / 3389) := by
    rw [show ((3389 / 2560) : ℝ) = ((2560 / 3389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (195653991 / 500000000) ≤ -Real.log (1731 / 2560) ∧
    -Real.log (1731 / 2560) ≤ (391307983 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 4291)) (n := 12)
    (lo := (195653991 / 500000000)) (hi := (391307983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1731) = 1/(1731 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-391307983 / 1000000000) (-195653991 / 500000000) (Real.log (1731 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5175903 / 25000000) ≤ -Real.log (1000000 / 1230027) ∧
    -Real.log (1000000 / 1230027) ≤ (207036121 / 1000000000) := by
  have h := checkLog_sound (w := (230027 / 2230027)) (n := 12)
    (lo := (5175903 / 25000000)) (hi := (207036121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230027 / 1000000) = 1/(1000000 / 1230027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5175903 / 25000000) (207036121 / 1000000000) (Real.log (1230027 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230027 / 1000000) = -Real.log (1000000 / 1230027) := by
    rw [show ((1230027 / 1000000) : ℝ) = ((1000000 / 1230027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (261399829 / 1000000000) ≤ -Real.log (769973 / 1000000) ∧
    -Real.log (769973 / 1000000) ≤ (26139983 / 100000000) := by
  have h := checkLog_sound (w := (230027 / 1769973)) (n := 12)
    (lo := (261399829 / 1000000000)) (hi := (26139983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769973) = 1/(769973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26139983 / 100000000) (-261399829 / 1000000000) (Real.log (769973 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20737833 / 100000000) ≤ -Real.log (62500 / 76903) ∧
    -Real.log (62500 / 76903) ≤ (207378331 / 1000000000) := by
  have h := checkLog_sound (w := (14403 / 139403)) (n := 12)
    (lo := (20737833 / 100000000)) (hi := (207378331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76903 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76903 / 62500) = 1/(62500 / 76903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20737833 / 100000000) (207378331 / 1000000000) (Real.log (76903 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (76903 / 62500) = -Real.log (62500 / 76903) := by
    rw [show ((76903 / 62500) : ℝ) = ((62500 / 76903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (261946751 / 1000000000) ≤ -Real.log (48097 / 62500) ∧
    -Real.log (48097 / 62500) ≤ (2046459 / 7812500) := by
  have h := checkLog_sound (w := (14403 / 110597)) (n := 12)
    (lo := (261946751 / 1000000000)) (hi := (2046459 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48097) = 1/(48097 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2046459 / 7812500) (-261946751 / 1000000000) (Real.log (48097 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38196151 / 250000000) ≤ -Real.log (500000 / 582537) ∧
    -Real.log (500000 / 582537) ≤ (30556921 / 200000000) := by
  have h := checkLog_sound (w := (82537 / 1082537)) (n := 12)
    (lo := (38196151 / 250000000)) (hi := (30556921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582537 / 500000) = 1/(500000 / 582537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38196151 / 250000000) (30556921 / 200000000) (Real.log (582537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (582537 / 500000) = -Real.log (500000 / 582537) := by
    rw [show ((582537 / 500000) : ℝ) = ((500000 / 582537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9020609 / 50000000) ≤ -Real.log (417463 / 500000) ∧
    -Real.log (417463 / 500000) ≤ (180412181 / 1000000000) := by
  have h := checkLog_sound (w := (82537 / 917463)) (n := 12)
    (lo := (9020609 / 50000000)) (hi := (180412181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417463) = 1/(417463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180412181 / 1000000000) (-9020609 / 50000000) (Real.log (417463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9565719 / 62500000) ≤ -Real.log (200000 / 233077) ∧
    -Real.log (200000 / 233077) ≤ (30610301 / 200000000) := by
  have h := checkLog_sound (w := (33077 / 433077)) (n := 12)
    (lo := (9565719 / 62500000)) (hi := (30610301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233077 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233077 / 200000) = 1/(200000 / 233077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9565719 / 62500000) (30610301 / 200000000) (Real.log (233077 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (233077 / 200000) = -Real.log (200000 / 233077) := by
    rw [show ((233077 / 200000) : ℝ) = ((200000 / 233077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90392369 / 500000000) ≤ -Real.log (166923 / 200000) ∧
    -Real.log (166923 / 200000) ≤ (180784739 / 1000000000) := by
  have h := checkLog_sound (w := (33077 / 366923)) (n := 12)
    (lo := (90392369 / 500000000)) (hi := (180784739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166923) = 1/(166923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180784739 / 1000000000) (-90392369 / 500000000) (Real.log (166923 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20994863 / 31250000) ≤ -Real.log (125000000000 / 244728480647) ∧
    -Real.log (125000000000 / 244728480647) ≤ (671835617 / 1000000000) := by
  have h := checkLog_sound (w := (119728480647 / 369728480647)) (n := 12)
    (lo := (20994863 / 31250000)) (hi := (671835617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244728480647 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244728480647 / 125000000000) = 1/(125000000000 / 244728480647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20994863 / 31250000) (671835617 / 1000000000) (Real.log (244728480647 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (244728480647 / 125000000000) = -Real.log (125000000000 / 244728480647) := by
    rw [show ((244728480647 / 125000000000) : ℝ) = ((125000000000 / 244728480647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (673145053 / 1000000000) ≤ -Real.log (50000000000 / 98019658861) ∧
    -Real.log (50000000000 / 98019658861) ≤ (336572527 / 500000000) := by
  have h := checkLog_sound (w := (48019658861 / 148019658861)) (n := 12)
    (lo := (673145053 / 1000000000)) (hi := (336572527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98019658861 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98019658861 / 50000000000) = 1/(50000000000 / 98019658861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (673145053 / 1000000000) (336572527 / 500000000) (Real.log (98019658861 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (98019658861 / 50000000000) = -Real.log (50000000000 / 98019658861) := by
    rw [show ((98019658861 / 50000000000) : ℝ) = ((50000000000 / 98019658861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (9368719 / 20000000) ≤ -Real.log (250000000000 / 399373419587) ∧
    -Real.log (250000000000 / 399373419587) ≤ (468435951 / 1000000000) := by
  have h := checkLog_sound (w := (149373419587 / 649373419587)) (n := 12)
    (lo := (9368719 / 20000000)) (hi := (468435951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399373419587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399373419587 / 250000000000) = 1/(250000000000 / 399373419587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9368719 / 20000000) (468435951 / 1000000000) (Real.log (399373419587 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399373419587 / 250000000000) = -Real.log (250000000000 / 399373419587) := by
    rw [show ((399373419587 / 250000000000) : ℝ) = ((250000000000 / 399373419587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (234662541 / 500000000) ≤ -Real.log (500000000000 / 799457346613) ∧
    -Real.log (500000000000 / 799457346613) ≤ (469325083 / 1000000000) := by
  have h := checkLog_sound (w := (299457346613 / 1299457346613)) (n := 12)
    (lo := (234662541 / 500000000)) (hi := (469325083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799457346613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799457346613 / 500000000000) = 1/(500000000000 / 799457346613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (234662541 / 500000000) (469325083 / 1000000000) (Real.log (799457346613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (799457346613 / 500000000000) = -Real.log (500000000000 / 799457346613) := by
    rw [show ((799457346613 / 500000000000) : ℝ) = ((500000000000 / 799457346613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (66639357 / 200000000) ≤ -Real.log (500000000000 / 697710934861) ∧
    -Real.log (500000000000 / 697710934861) ≤ (166598393 / 500000000) := by
  have h := checkLog_sound (w := (197710934861 / 1197710934861)) (n := 12)
    (lo := (66639357 / 200000000)) (hi := (166598393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697710934861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697710934861 / 500000000000) = 1/(500000000000 / 697710934861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (66639357 / 200000000) (166598393 / 500000000) (Real.log (697710934861 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (697710934861 / 500000000000) = -Real.log (500000000000 / 697710934861) := by
    rw [show ((697710934861 / 500000000000) : ℝ) = ((500000000000 / 697710934861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (166918121 / 500000000) ≤ -Real.log (250000000000 / 349078617087) ∧
    -Real.log (250000000000 / 349078617087) ≤ (333836243 / 1000000000) := by
  have h := checkLog_sound (w := (99078617087 / 599078617087)) (n := 12)
    (lo := (166918121 / 500000000)) (hi := (333836243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349078617087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349078617087 / 250000000000) = 1/(250000000000 / 349078617087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (166918121 / 500000000) (333836243 / 1000000000) (Real.log (349078617087 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (349078617087 / 250000000000) = -Real.log (250000000000 / 349078617087) := by
    rw [show ((349078617087 / 250000000000) : ℝ) = ((250000000000 / 349078617087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27733233 / 1000000000) ≤ -Real.log (38905912071 / 40000000000) ∧
    -Real.log (38905912071 / 40000000000) ≤ (13866617 / 500000000) := by
  have h := checkLog_sound (w := (1094087929 / 78905912071)) (n := 12)
    (lo := (27733233 / 1000000000)) (hi := (13866617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38905912071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38905912071) = 1/(38905912071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13866617 / 500000000) (-27733233 / 1000000000) (Real.log (38905912071 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3453447 / 125000000) ≤ -Real.log (243187643631 / 250000000000) ∧
    -Real.log (243187643631 / 250000000000) ≤ (27627577 / 1000000000) := by
  have h := checkLog_sound (w := (6812356369 / 493187643631)) (n := 12)
    (lo := (3453447 / 125000000)) (hi := (27627577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243187643631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243187643631) = 1/(243187643631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27627577 / 1000000000) (-3453447 / 125000000) (Real.log (243187643631 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell126

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell127Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell127
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

theorem reflection_log_1_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8780317 / 31250000) ≤ -Real.log (5120 / 6781) ∧
    -Real.log (5120 / 6781) ≤ (56194029 / 200000000) := by
  have h := checkLog_sound (w := (1661 / 11901)) (n := 12)
    (lo := (8780317 / 31250000)) (hi := (56194029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6781 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6781 / 5120) = 1/(5120 / 6781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8780317 / 31250000) (56194029 / 200000000) (Real.log (6781 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6781 / 5120) = -Real.log (5120 / 6781) := by
    rw [show ((6781 / 5120) : ℝ) = ((5120 / 6781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (392174909 / 1000000000) ≤ -Real.log (3459 / 5120) ∧
    -Real.log (3459 / 5120) ≤ (39217491 / 100000000) := by
  have h := checkLog_sound (w := (1661 / 8579)) (n := 12)
    (lo := (392174909 / 1000000000)) (hi := (39217491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3459) = 1/(3459 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-39217491 / 100000000) (-392174909 / 1000000000) (Real.log (3459 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207377517 / 1000000000) ≤ -Real.log (1000000 / 1230447) ∧
    -Real.log (1000000 / 1230447) ≤ (103688759 / 500000000) := by
  have h := checkLog_sound (w := (230447 / 2230447)) (n := 12)
    (lo := (207377517 / 1000000000)) (hi := (103688759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230447 / 1000000) = 1/(1000000 / 1230447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207377517 / 1000000000) (103688759 / 500000000) (Real.log (1230447 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230447 / 1000000) = -Real.log (1000000 / 1230447) := by
    rw [show ((1230447 / 1000000) : ℝ) = ((1000000 / 1230447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65486363 / 250000000) ≤ -Real.log (769553 / 1000000) ∧
    -Real.log (769553 / 1000000) ≤ (261945453 / 1000000000) := by
  have h := checkLog_sound (w := (230447 / 1769553)) (n := 12)
    (lo := (65486363 / 250000000)) (hi := (261945453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769553) = 1/(769553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-261945453 / 1000000000) (-65486363 / 250000000) (Real.log (769553 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207719611 / 1000000000) ≤ -Real.log (250000 / 307717) ∧
    -Real.log (250000 / 307717) ≤ (51929903 / 250000000) := by
  have h := checkLog_sound (w := (57717 / 557717)) (n := 12)
    (lo := (207719611 / 1000000000)) (hi := (51929903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307717 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307717 / 250000) = 1/(250000 / 307717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207719611 / 1000000000) (51929903 / 250000000) (Real.log (307717 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307717 / 250000) = -Real.log (250000 / 307717) := by
    rw [show ((307717 / 250000) : ℝ) = ((250000 / 307717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512681 / 1953125) ≤ -Real.log (192283 / 250000) ∧
    -Real.log (192283 / 250000) ≤ (262492673 / 1000000000) := by
  have h := checkLog_sound (w := (57717 / 442283)) (n := 12)
    (lo := (512681 / 1953125)) (hi := (262492673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192283) = 1/(192283 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-262492673 / 1000000000) (-512681 / 1953125) (Real.log (192283 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76525323 / 500000000) ≤ -Real.log (125000 / 145673) ∧
    -Real.log (125000 / 145673) ≤ (153050647 / 1000000000) := by
  have h := checkLog_sound (w := (20673 / 270673)) (n := 12)
    (lo := (76525323 / 500000000)) (hi := (153050647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145673 / 125000) = 1/(125000 / 145673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76525323 / 500000000) (153050647 / 1000000000) (Real.log (145673 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145673 / 125000) = -Real.log (125000 / 145673) := by
    rw [show ((145673 / 125000) : ℝ) = ((125000 / 145673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9039177 / 50000000) ≤ -Real.log (104327 / 125000) ∧
    -Real.log (104327 / 125000) ≤ (180783541 / 1000000000) := by
  have h := checkLog_sound (w := (20673 / 229327)) (n := 12)
    (lo := (9039177 / 50000000)) (hi := (180783541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104327) = 1/(104327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180783541 / 1000000000) (-9039177 / 50000000) (Real.log (104327 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153318333 / 1000000000) ≤ -Real.log (15625 / 18214) ∧
    -Real.log (15625 / 18214) ≤ (76659167 / 500000000) := by
  have h := checkLog_sound (w := (2589 / 33839)) (n := 12)
    (lo := (153318333 / 1000000000)) (hi := (76659167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18214 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18214 / 15625) = 1/(15625 / 18214) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153318333 / 1000000000) (76659167 / 500000000) (Real.log (18214 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18214 / 15625) = -Real.log (15625 / 18214) := by
    rw [show ((18214 / 15625) : ℝ) = ((15625 / 18214) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90578717 / 500000000) ≤ -Real.log (13036 / 15625) ∧
    -Real.log (13036 / 15625) ≤ (36231487 / 200000000) := by
  have h := checkLog_sound (w := (2589 / 28661)) (n := 12)
    (lo := (90578717 / 500000000)) (hi := (36231487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13036) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13036) = 1/(13036 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36231487 / 200000000) (-90578717 / 500000000) (Real.log (13036 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673145053 / 1000000000) ≤ -Real.log (500000000000 / 980196588609) ∧
    -Real.log (500000000000 / 980196588609) ≤ (336572527 / 500000000) := by
  have h := checkLog_sound (w := (480196588609 / 1480196588609)) (n := 12)
    (lo := (673145053 / 1000000000)) (hi := (336572527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980196588609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980196588609 / 500000000000) = 1/(500000000000 / 980196588609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673145053 / 1000000000) (336572527 / 500000000) (Real.log (980196588609 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980196588609 / 500000000000) = -Real.log (500000000000 / 980196588609) := by
    rw [show ((980196588609 / 500000000000) : ℝ) = ((500000000000 / 980196588609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (674455047 / 1000000000) ≤ -Real.log (250000000000 / 490740740741) ∧
    -Real.log (250000000000 / 490740740741) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (240740740741 / 740740740741)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490740740741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490740740741 / 250000000000) = 1/(250000000000 / 490740740741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (490740740741 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (490740740741 / 250000000000) = -Real.log (250000000000 / 490740740741) := by
    rw [show ((490740740741 / 250000000000) : ℝ) = ((250000000000 / 490740740741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (46932297 / 100000000) ≤ -Real.log (62500000000 / 99931957253) ∧
    -Real.log (62500000000 / 99931957253) ≤ (469322971 / 1000000000) := by
  have h := checkLog_sound (w := (37431957253 / 162431957253)) (n := 12)
    (lo := (46932297 / 100000000)) (hi := (469322971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99931957253 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99931957253 / 62500000000) = 1/(62500000000 / 99931957253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46932297 / 100000000) (469322971 / 1000000000) (Real.log (99931957253 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (99931957253 / 62500000000) = -Real.log (62500000000 / 99931957253) := by
    rw [show ((99931957253 / 62500000000) : ℝ) = ((62500000000 / 99931957253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117553071 / 250000000) ≤ -Real.log (125000000000 / 200041735359) ∧
    -Real.log (125000000000 / 200041735359) ≤ (94042457 / 200000000) := by
  have h := checkLog_sound (w := (75041735359 / 325041735359)) (n := 12)
    (lo := (117553071 / 250000000)) (hi := (94042457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200041735359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200041735359 / 125000000000) = 1/(125000000000 / 200041735359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (117553071 / 250000000) (94042457 / 200000000) (Real.log (200041735359 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (200041735359 / 125000000000) = -Real.log (125000000000 / 200041735359) := by
    rw [show ((200041735359 / 125000000000) : ℝ) = ((125000000000 / 200041735359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (166917093 / 500000000) ≤ -Real.log (250000000000 / 349077899297) ∧
    -Real.log (250000000000 / 349077899297) ≤ (333834187 / 1000000000) := by
  have h := checkLog_sound (w := (99077899297 / 599077899297)) (n := 12)
    (lo := (166917093 / 500000000)) (hi := (333834187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349077899297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349077899297 / 250000000000) = 1/(250000000000 / 349077899297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166917093 / 500000000) (333834187 / 1000000000) (Real.log (349077899297 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349077899297 / 250000000000) = -Real.log (250000000000 / 349077899297) := by
    rw [show ((349077899297 / 250000000000) : ℝ) = ((250000000000 / 349077899297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41809471 / 125000000) ≤ -Real.log (500000000000 / 698603866217) ∧
    -Real.log (500000000000 / 698603866217) ≤ (334475769 / 1000000000) := by
  have h := checkLog_sound (w := (198603866217 / 1198603866217)) (n := 12)
    (lo := (41809471 / 125000000)) (hi := (334475769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698603866217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698603866217 / 500000000000) = 1/(500000000000 / 698603866217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41809471 / 125000000) (334475769 / 1000000000) (Real.log (698603866217 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (698603866217 / 500000000000) = -Real.log (500000000000 / 698603866217) := by
    rw [show ((698603866217 / 500000000000) : ℝ) = ((500000000000 / 698603866217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27839101 / 1000000000) ≤ -Real.log (237437704 / 244140625) ∧
    -Real.log (237437704 / 244140625) ≤ (13919551 / 500000000) := by
  have h := checkLog_sound (w := (6702921 / 481578329)) (n := 12)
    (lo := (27839101 / 1000000000)) (hi := (13919551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 237437704) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 237437704) = 1/(237437704 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13919551 / 500000000) (-27839101 / 1000000000) (Real.log (237437704 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27732893 / 1000000000) ≤ -Real.log (15197627071 / 15625000000) ∧
    -Real.log (15197627071 / 15625000000) ≤ (13866447 / 500000000) := by
  have h := checkLog_sound (w := (427372929 / 30822627071)) (n := 12)
    (lo := (27732893 / 1000000000)) (hi := (13866447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15197627071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15197627071) = 1/(15197627071 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13866447 / 500000000) (-27732893 / 1000000000) (Real.log (15197627071 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell127

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell128Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell128
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

theorem reflection_log_1_neg : (140927289 / 500000000) ≤ -Real.log (5120 / 6787) ∧
    -Real.log (5120 / 6787) ≤ (281854579 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 11907)) (n := 12)
    (lo := (140927289 / 500000000)) (hi := (281854579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 5120) = 1/(5120 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140927289 / 500000000) (281854579 / 1000000000) (Real.log (6787 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6787 / 5120) = -Real.log (5120 / 6787) := by
    rw [show ((6787 / 5120) : ℝ) = ((5120 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19695551 / 50000000) ≤ -Real.log (3453 / 5120) ∧
    -Real.log (3453 / 5120) ≤ (393911021 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 8573)) (n := 12)
    (lo := (19695551 / 50000000)) (hi := (393911021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3453) = 1/(3453 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393911021 / 1000000000) (-19695551 / 50000000) (Real.log (3453 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207718799 / 1000000000) ≤ -Real.log (1000000 / 1230867) ∧
    -Real.log (1000000 / 1230867) ≤ (519297 / 2500000) := by
  have h := checkLog_sound (w := (230867 / 2230867)) (n := 12)
    (lo := (207718799 / 1000000000)) (hi := (519297 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230867 / 1000000) = 1/(1000000 / 1230867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207718799 / 1000000000) (519297 / 2500000) (Real.log (1230867 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230867 / 1000000) = -Real.log (1000000 / 1230867) := by
    rw [show ((1230867 / 1000000) : ℝ) = ((1000000 / 1230867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65622843 / 250000000) ≤ -Real.log (769133 / 1000000) ∧
    -Real.log (769133 / 1000000) ≤ (262491373 / 1000000000) := by
  have h := checkLog_sound (w := (230867 / 1769133)) (n := 12)
    (lo := (65622843 / 250000000)) (hi := (262491373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769133) = 1/(769133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-262491373 / 1000000000) (-65622843 / 250000000) (Real.log (769133 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (52015397 / 250000000) ≤ -Real.log (1000000 / 1231289) ∧
    -Real.log (1000000 / 1231289) ≤ (208061589 / 1000000000) := by
  have h := checkLog_sound (w := (231289 / 2231289)) (n := 12)
    (lo := (52015397 / 250000000)) (hi := (208061589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231289 / 1000000) = 1/(1000000 / 1231289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (52015397 / 250000000) (208061589 / 1000000000) (Real.log (1231289 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1231289 / 1000000) = -Real.log (1000000 / 1231289) := by
    rw [show ((1231289 / 1000000) : ℝ) = ((1000000 / 1231289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4110003 / 15625000) ≤ -Real.log (768711 / 1000000) ∧
    -Real.log (768711 / 1000000) ≤ (263040193 / 1000000000) := by
  have h := checkLog_sound (w := (231289 / 1768711)) (n := 12)
    (lo := (4110003 / 15625000)) (hi := (263040193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768711) = 1/(768711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-263040193 / 1000000000) (-4110003 / 15625000) (Real.log (768711 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6132699 / 40000000) ≤ -Real.log (200000 / 233139) ∧
    -Real.log (200000 / 233139) ≤ (38329369 / 250000000) := by
  have h := checkLog_sound (w := (33139 / 433139)) (n := 12)
    (lo := (6132699 / 40000000)) (hi := (38329369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233139 / 200000) = 1/(200000 / 233139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6132699 / 40000000) (38329369 / 250000000) (Real.log (233139 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233139 / 200000) = -Real.log (200000 / 233139) := by
    rw [show ((233139 / 200000) : ℝ) = ((200000 / 233139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (45289059 / 250000000) ≤ -Real.log (166861 / 200000) ∧
    -Real.log (166861 / 200000) ≤ (181156237 / 1000000000) := by
  have h := checkLog_sound (w := (33139 / 366861)) (n := 12)
    (lo := (45289059 / 250000000)) (hi := (181156237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166861) = 1/(166861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-181156237 / 1000000000) (-45289059 / 250000000) (Real.log (166861 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153584233 / 1000000000) ≤ -Real.log (500000 / 583003) ∧
    -Real.log (500000 / 583003) ≤ (76792117 / 500000000) := by
  have h := checkLog_sound (w := (83003 / 1083003)) (n := 12)
    (lo := (153584233 / 1000000000)) (hi := (76792117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583003 / 500000) = 1/(500000 / 583003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153584233 / 1000000000) (76792117 / 500000000) (Real.log (583003 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (583003 / 500000) = -Real.log (500000 / 583003) := by
    rw [show ((583003 / 500000) : ℝ) = ((500000 / 583003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18152907 / 100000000) ≤ -Real.log (416997 / 500000) ∧
    -Real.log (416997 / 500000) ≤ (181529071 / 1000000000) := by
  have h := checkLog_sound (w := (83003 / 916997)) (n := 12)
    (lo := (18152907 / 100000000)) (hi := (181529071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416997) = 1/(416997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-181529071 / 1000000000) (-18152907 / 100000000) (Real.log (416997 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674455047 / 1000000000) ≤ -Real.log (500000000000 / 981481481481) ∧
    -Real.log (500000000000 / 981481481481) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (481481481481 / 1481481481481)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981481481481 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981481481481 / 500000000000) = 1/(500000000000 / 981481481481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (981481481481 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981481481481 / 500000000000) = -Real.log (500000000000 / 981481481481) := by
    rw [show ((981481481481 / 500000000000) : ℝ) = ((500000000000 / 981481481481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (675765599 / 1000000000) ≤ -Real.log (500000000000 / 982768607009) ∧
    -Real.log (500000000000 / 982768607009) ≤ (844707 / 1250000) := by
  have h := checkLog_sound (w := (482768607009 / 1482768607009)) (n := 12)
    (lo := (675765599 / 1000000000)) (hi := (844707 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982768607009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982768607009 / 500000000000) = 1/(500000000000 / 982768607009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (675765599 / 1000000000) (844707 / 1250000) (Real.log (982768607009 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (982768607009 / 500000000000) = -Real.log (500000000000 / 982768607009) := by
    rw [show ((982768607009 / 500000000000) : ℝ) = ((500000000000 / 982768607009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (470210171 / 1000000000) ≤ -Real.log (500000000000 / 800165251003) ∧
    -Real.log (500000000000 / 800165251003) ≤ (117552543 / 250000000) := by
  have h := checkLog_sound (w := (300165251003 / 1300165251003)) (n := 12)
    (lo := (470210171 / 1000000000)) (hi := (117552543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800165251003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800165251003 / 500000000000) = 1/(500000000000 / 800165251003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (470210171 / 1000000000) (117552543 / 250000000) (Real.log (800165251003 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (800165251003 / 500000000000) = -Real.log (500000000000 / 800165251003) := by
    rw [show ((800165251003 / 500000000000) : ℝ) = ((500000000000 / 800165251003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23555089 / 50000000) ≤ -Real.log (500000000000 / 800879003943) ∧
    -Real.log (500000000000 / 800879003943) ≤ (471101781 / 1000000000) := by
  have h := checkLog_sound (w := (300879003943 / 1300879003943)) (n := 12)
    (lo := (23555089 / 50000000)) (hi := (471101781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800879003943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800879003943 / 500000000000) = 1/(500000000000 / 800879003943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23555089 / 50000000) (471101781 / 1000000000) (Real.log (800879003943 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (800879003943 / 500000000000) = -Real.log (500000000000 / 800879003943) := by
    rw [show ((800879003943 / 500000000000) : ℝ) = ((500000000000 / 800879003943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (334473711 / 1000000000) ≤ -Real.log (500000000000 / 698602429567) ∧
    -Real.log (500000000000 / 698602429567) ≤ (20904607 / 62500000) := by
  have h := checkLog_sound (w := (198602429567 / 1198602429567)) (n := 12)
    (lo := (334473711 / 1000000000)) (hi := (20904607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698602429567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698602429567 / 500000000000) = 1/(500000000000 / 698602429567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (334473711 / 1000000000) (20904607 / 62500000) (Real.log (698602429567 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (698602429567 / 500000000000) = -Real.log (500000000000 / 698602429567) := by
    rw [show ((698602429567 / 500000000000) : ℝ) = ((500000000000 / 698602429567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41889163 / 125000000) ≤ -Real.log (500000000000 / 699049393641) ∧
    -Real.log (500000000000 / 699049393641) ≤ (67022661 / 200000000) := by
  have h := checkLog_sound (w := (199049393641 / 1199049393641)) (n := 12)
    (lo := (41889163 / 125000000)) (hi := (67022661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699049393641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699049393641 / 500000000000) = 1/(500000000000 / 699049393641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41889163 / 125000000) (67022661 / 200000000) (Real.log (699049393641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (699049393641 / 500000000000) = -Real.log (500000000000 / 699049393641) := by
    rw [show ((699049393641 / 500000000000) : ℝ) = ((500000000000 / 699049393641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27944837 / 1000000000) ≤ -Real.log (243110501991 / 250000000000) ∧
    -Real.log (243110501991 / 250000000000) ≤ (13972419 / 500000000) := by
  have h := checkLog_sound (w := (6889498009 / 493110501991)) (n := 12)
    (lo := (27944837 / 1000000000)) (hi := (13972419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243110501991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243110501991) = 1/(243110501991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13972419 / 500000000) (-27944837 / 1000000000) (Real.log (243110501991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (695969 / 25000000) ≤ -Real.log (38901806679 / 40000000000) ∧
    -Real.log (38901806679 / 40000000000) ≤ (27838761 / 1000000000) := by
  have h := checkLog_sound (w := (1098193321 / 78901806679)) (n := 12)
    (lo := (695969 / 25000000)) (hi := (27838761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38901806679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38901806679) = 1/(38901806679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27838761 / 1000000000) (-695969 / 25000000) (Real.log (38901806679 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell128

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell129Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell129
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

theorem reflection_log_1_neg : (141148251 / 500000000) ≤ -Real.log (512 / 679) ∧
    -Real.log (512 / 679) ≤ (282296503 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1191)) (n := 12)
    (lo := (141148251 / 500000000)) (hi := (282296503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 512) = 1/(512 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (141148251 / 500000000) (282296503 / 1000000000) (Real.log (679 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (679 / 512) = -Real.log (512 / 679) := by
    rw [show ((679 / 512) : ℝ) = ((512 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24673763 / 62500000) ≤ -Real.log (345 / 512) ∧
    -Real.log (345 / 512) ≤ (394780209 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 857)) (n := 12)
    (lo := (24673763 / 62500000)) (hi := (394780209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 345) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 345) = 1/(345 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-394780209 / 1000000000) (-24673763 / 62500000) (Real.log (345 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140927289 / 500000000) ≤ -Real.log (5120 / 6787) ∧
    -Real.log (5120 / 6787) ≤ (281854579 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 11907)) (n := 12)
    (lo := (140927289 / 500000000)) (hi := (281854579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 5120) = 1/(5120 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140927289 / 500000000) (281854579 / 1000000000) (Real.log (6787 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6787 / 5120) = -Real.log (5120 / 6787) := by
    rw [show ((6787 / 5120) : ℝ) = ((5120 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19695551 / 50000000) ≤ -Real.log (3453 / 5120) ∧
    -Real.log (3453 / 5120) ≤ (393911021 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 8573)) (n := 12)
    (lo := (19695551 / 50000000)) (hi := (393911021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3453) = 1/(3453 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393911021 / 1000000000) (-19695551 / 50000000) (Real.log (3453 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8322431 / 40000000) ≤ -Real.log (125000 / 153911) ∧
    -Real.log (125000 / 153911) ≤ (26007597 / 125000000) := by
  have h := checkLog_sound (w := (28911 / 278911)) (n := 12)
    (lo := (8322431 / 40000000)) (hi := (26007597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153911 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153911 / 125000) = 1/(125000 / 153911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8322431 / 40000000) (26007597 / 125000000) (Real.log (153911 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (153911 / 125000) = -Real.log (125000 / 153911) := by
    rw [show ((153911 / 125000) : ℝ) = ((125000 / 153911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (263038891 / 1000000000) ≤ -Real.log (96089 / 125000) ∧
    -Real.log (96089 / 125000) ≤ (65759723 / 250000000) := by
  have h := checkLog_sound (w := (28911 / 221089)) (n := 12)
    (lo := (263038891 / 1000000000)) (hi := (65759723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96089) = 1/(96089 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-65759723 / 250000000) (-263038891 / 1000000000) (Real.log (96089 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41680527 / 200000000) ≤ -Real.log (1000000 / 1231709) ∧
    -Real.log (1000000 / 1231709) ≤ (52100659 / 250000000) := by
  have h := checkLog_sound (w := (231709 / 2231709)) (n := 12)
    (lo := (41680527 / 200000000)) (hi := (52100659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231709 / 1000000) = 1/(1000000 / 1231709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41680527 / 200000000) (52100659 / 250000000) (Real.log (1231709 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1231709 / 1000000) = -Real.log (1000000 / 1231709) := by
    rw [show ((1231709 / 1000000) : ℝ) = ((1000000 / 1231709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (263586711 / 1000000000) ≤ -Real.log (768291 / 1000000) ∧
    -Real.log (768291 / 1000000) ≤ (32948339 / 125000000) := by
  have h := checkLog_sound (w := (231709 / 1768291)) (n := 12)
    (lo := (263586711 / 1000000000)) (hi := (32948339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768291) = 1/(768291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32948339 / 125000000) (-263586711 / 1000000000) (Real.log (768291 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9598961 / 62500000) ≤ -Real.log (200000 / 233201) ∧
    -Real.log (200000 / 233201) ≤ (153583377 / 1000000000) := by
  have h := checkLog_sound (w := (33201 / 433201)) (n := 12)
    (lo := (9598961 / 62500000)) (hi := (153583377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233201 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233201 / 200000) = 1/(200000 / 233201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9598961 / 62500000) (153583377 / 1000000000) (Real.log (233201 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233201 / 200000) = -Real.log (200000 / 233201) := by
    rw [show ((233201 / 200000) : ℝ) = ((200000 / 233201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (181527871 / 1000000000) ≤ -Real.log (166799 / 200000) ∧
    -Real.log (166799 / 200000) ≤ (2836373 / 15625000) := by
  have h := checkLog_sound (w := (33201 / 366799)) (n := 12)
    (lo := (181527871 / 1000000000)) (hi := (2836373 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166799) = 1/(166799 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2836373 / 15625000) (-181527871 / 1000000000) (Real.log (166799 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3846273 / 25000000) ≤ -Real.log (1000000 / 1166317) ∧
    -Real.log (1000000 / 1166317) ≤ (153850921 / 1000000000) := by
  have h := checkLog_sound (w := (166317 / 2166317)) (n := 12)
    (lo := (3846273 / 25000000)) (hi := (153850921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166317 / 1000000) = 1/(1000000 / 1166317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3846273 / 25000000) (153850921 / 1000000000) (Real.log (1166317 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1166317 / 1000000) = -Real.log (1000000 / 1166317) := by
    rw [show ((1166317 / 1000000) : ℝ) = ((1000000 / 1166317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45475511 / 250000000) ≤ -Real.log (833683 / 1000000) ∧
    -Real.log (833683 / 1000000) ≤ (36380409 / 200000000) := by
  have h := checkLog_sound (w := (166317 / 1833683)) (n := 12)
    (lo := (45475511 / 250000000)) (hi := (36380409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833683) = 1/(833683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36380409 / 200000000) (-45475511 / 250000000) (Real.log (833683 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675765599 / 1000000000) ≤ -Real.log (15625000000 / 30711518969) ∧
    -Real.log (15625000000 / 30711518969) ≤ (844707 / 1250000) := by
  have h := checkLog_sound (w := (15086518969 / 46336518969)) (n := 12)
    (lo := (675765599 / 1000000000)) (hi := (844707 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30711518969 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30711518969 / 15625000000) = 1/(15625000000 / 30711518969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675765599 / 1000000000) (844707 / 1250000) (Real.log (30711518969 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30711518969 / 15625000000) = -Real.log (15625000000 / 30711518969) := by
    rw [show ((30711518969 / 15625000000) : ℝ) = ((15625000000 / 30711518969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67707671 / 100000000) ≤ -Real.log (100000000000 / 196811594203) ∧
    -Real.log (100000000000 / 196811594203) ≤ (677076711 / 1000000000) := by
  have h := checkLog_sound (w := (96811594203 / 296811594203)) (n := 12)
    (lo := (67707671 / 100000000)) (hi := (677076711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196811594203 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196811594203 / 100000000000) = 1/(100000000000 / 196811594203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (67707671 / 100000000) (677076711 / 1000000000) (Real.log (196811594203 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (196811594203 / 100000000000) = -Real.log (100000000000 / 196811594203) := by
    rw [show ((196811594203 / 100000000000) : ℝ) = ((100000000000 / 196811594203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (471099667 / 1000000000) ≤ -Real.log (250000000000 / 400438655829) ∧
    -Real.log (250000000000 / 400438655829) ≤ (117774917 / 250000000) := by
  have h := checkLog_sound (w := (150438655829 / 650438655829)) (n := 12)
    (lo := (471099667 / 1000000000)) (hi := (117774917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400438655829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400438655829 / 250000000000) = 1/(250000000000 / 400438655829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (471099667 / 1000000000) (117774917 / 250000000) (Real.log (400438655829 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (400438655829 / 250000000000) = -Real.log (250000000000 / 400438655829) := by
    rw [show ((400438655829 / 250000000000) : ℝ) = ((250000000000 / 400438655829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (471989347 / 1000000000) ≤ -Real.log (50000000000 / 80159015269) ∧
    -Real.log (50000000000 / 80159015269) ≤ (117997337 / 250000000) := by
  have h := checkLog_sound (w := (30159015269 / 130159015269)) (n := 12)
    (lo := (471989347 / 1000000000)) (hi := (117997337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80159015269 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80159015269 / 50000000000) = 1/(50000000000 / 80159015269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (471989347 / 1000000000) (117997337 / 250000000) (Real.log (80159015269 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (80159015269 / 50000000000) = -Real.log (50000000000 / 80159015269) := by
    rw [show ((80159015269 / 50000000000) : ℝ) = ((50000000000 / 80159015269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (335111247 / 1000000000) ≤ -Real.log (250000000000 / 349523977961) ∧
    -Real.log (250000000000 / 349523977961) ≤ (20944453 / 62500000) := by
  have h := checkLog_sound (w := (99523977961 / 599523977961)) (n := 12)
    (lo := (335111247 / 1000000000)) (hi := (20944453 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349523977961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349523977961 / 250000000000) = 1/(250000000000 / 349523977961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (335111247 / 1000000000) (20944453 / 62500000) (Real.log (349523977961 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349523977961 / 250000000000) = -Real.log (250000000000 / 349523977961) := by
    rw [show ((349523977961 / 250000000000) : ℝ) = ((250000000000 / 349523977961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (67150593 / 200000000) ≤ -Real.log (500000000000 / 699496691189) ∧
    -Real.log (500000000000 / 699496691189) ≤ (167876483 / 500000000) := by
  have h := checkLog_sound (w := (199496691189 / 1199496691189)) (n := 12)
    (lo := (67150593 / 200000000)) (hi := (167876483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699496691189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699496691189 / 500000000000) = 1/(500000000000 / 699496691189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (67150593 / 200000000) (167876483 / 500000000) (Real.log (699496691189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (699496691189 / 500000000000) = -Real.log (500000000000 / 699496691189) := by
    rw [show ((699496691189 / 500000000000) : ℝ) = ((500000000000 / 699496691189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7012781 / 250000000) ≤ -Real.log (972338655511 / 1000000000000) ∧
    -Real.log (972338655511 / 1000000000000) ≤ (224409 / 8000000) := by
  have h := checkLog_sound (w := (27661344489 / 1972338655511)) (n := 12)
    (lo := (7012781 / 250000000)) (hi := (224409 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972338655511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972338655511) = 1/(972338655511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-224409 / 8000000) (-7012781 / 250000000) (Real.log (972338655511 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5588899 / 200000000) ≤ -Real.log (38897693599 / 40000000000) ∧
    -Real.log (38897693599 / 40000000000) ≤ (1746531 / 62500000) := by
  have h := checkLog_sound (w := (1102306401 / 78897693599)) (n := 12)
    (lo := (5588899 / 200000000)) (hi := (1746531 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38897693599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38897693599) = 1/(38897693599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1746531 / 62500000) (-5588899 / 200000000) (Real.log (38897693599 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell129

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell130Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell130
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

theorem reflection_log_1_neg : (282738231 / 1000000000) ≤ -Real.log (5120 / 6793) ∧
    -Real.log (5120 / 6793) ≤ (35342279 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 11913)) (n := 12)
    (lo := (282738231 / 1000000000)) (hi := (35342279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6793 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6793 / 5120) = 1/(5120 / 6793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (282738231 / 1000000000) (35342279 / 125000000) (Real.log (6793 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6793 / 5120) = -Real.log (5120 / 6793) := by
    rw [show ((6793 / 5120) : ℝ) = ((5120 / 6793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (395650151 / 1000000000) ≤ -Real.log (3447 / 5120) ∧
    -Real.log (3447 / 5120) ≤ (49456269 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 8567)) (n := 12)
    (lo := (395650151 / 1000000000)) (hi := (49456269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3447) = 1/(3447 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49456269 / 125000000) (-395650151 / 1000000000) (Real.log (3447 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (141148251 / 500000000) ≤ -Real.log (512 / 679) ∧
    -Real.log (512 / 679) ≤ (282296503 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1191)) (n := 12)
    (lo := (141148251 / 500000000)) (hi := (282296503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 512) = 1/(512 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (141148251 / 500000000) (282296503 / 1000000000) (Real.log (679 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (679 / 512) = -Real.log (512 / 679) := by
    rw [show ((679 / 512) : ℝ) = ((512 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24673763 / 62500000) ≤ -Real.log (345 / 512) ∧
    -Real.log (345 / 512) ≤ (394780209 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 857)) (n := 12)
    (lo := (24673763 / 62500000)) (hi := (394780209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 345) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 345) = 1/(345 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-394780209 / 1000000000) (-24673763 / 62500000) (Real.log (345 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6512557 / 31250000) ≤ -Real.log (250000 / 307927) ∧
    -Real.log (250000 / 307927) ≤ (8336073 / 40000000) := by
  have h := checkLog_sound (w := (57927 / 557927)) (n := 12)
    (lo := (6512557 / 31250000)) (hi := (8336073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307927 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307927 / 250000) = 1/(250000 / 307927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6512557 / 31250000) (8336073 / 40000000) (Real.log (307927 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (307927 / 250000) = -Real.log (250000 / 307927) := by
    rw [show ((307927 / 250000) : ℝ) = ((250000 / 307927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (263585409 / 1000000000) ≤ -Real.log (192073 / 250000) ∧
    -Real.log (192073 / 250000) ≤ (26358541 / 100000000) := by
  have h := checkLog_sound (w := (57927 / 442073)) (n := 12)
    (lo := (263585409 / 1000000000)) (hi := (26358541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192073) = 1/(192073 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26358541 / 100000000) (-263585409 / 1000000000) (Real.log (192073 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (208743567 / 1000000000) ≤ -Real.log (1000000 / 1232129) ∧
    -Real.log (1000000 / 1232129) ≤ (13046473 / 62500000) := by
  have h := checkLog_sound (w := (232129 / 2232129)) (n := 12)
    (lo := (208743567 / 1000000000)) (hi := (13046473 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232129 / 1000000) = 1/(1000000 / 1232129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (208743567 / 1000000000) (13046473 / 62500000) (Real.log (1232129 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1232129 / 1000000) = -Real.log (1000000 / 1232129) := by
    rw [show ((1232129 / 1000000) : ℝ) = ((1000000 / 1232129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33016691 / 125000000) ≤ -Real.log (767871 / 1000000) ∧
    -Real.log (767871 / 1000000) ≤ (264133529 / 1000000000) := by
  have h := checkLog_sound (w := (232129 / 1767871)) (n := 12)
    (lo := (33016691 / 125000000)) (hi := (264133529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767871) = 1/(767871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-264133529 / 1000000000) (-33016691 / 125000000) (Real.log (767871 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153850063 / 1000000000) ≤ -Real.log (250000 / 291579) ∧
    -Real.log (250000 / 291579) ≤ (9615629 / 62500000) := by
  have h := checkLog_sound (w := (41579 / 541579)) (n := 12)
    (lo := (153850063 / 1000000000)) (hi := (9615629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291579 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291579 / 250000) = 1/(250000 / 291579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153850063 / 1000000000) (9615629 / 62500000) (Real.log (291579 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (291579 / 250000) = -Real.log (250000 / 291579) := by
    rw [show ((291579 / 250000) : ℝ) = ((250000 / 291579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36380169 / 200000000) ≤ -Real.log (208421 / 250000) ∧
    -Real.log (208421 / 250000) ≤ (90950423 / 500000000) := by
  have h := checkLog_sound (w := (41579 / 458421)) (n := 12)
    (lo := (36380169 / 200000000)) (hi := (90950423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208421) = 1/(208421 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-90950423 / 500000000) (-36380169 / 200000000) (Real.log (208421 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4816173 / 31250000) ≤ -Real.log (250000 / 291657) ∧
    -Real.log (250000 / 291657) ≤ (154117537 / 1000000000) := by
  have h := checkLog_sound (w := (41657 / 541657)) (n := 12)
    (lo := (4816173 / 31250000)) (hi := (154117537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291657 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291657 / 250000) = 1/(250000 / 291657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4816173 / 31250000) (154117537 / 1000000000) (Real.log (291657 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (291657 / 250000) = -Real.log (250000 / 291657) := by
    rw [show ((291657 / 250000) : ℝ) = ((250000 / 291657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (182275157 / 1000000000) ≤ -Real.log (208343 / 250000) ∧
    -Real.log (208343 / 250000) ≤ (91137579 / 500000000) := by
  have h := checkLog_sound (w := (41657 / 458343)) (n := 12)
    (lo := (182275157 / 1000000000)) (hi := (91137579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208343) = 1/(208343 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91137579 / 500000000) (-182275157 / 1000000000) (Real.log (208343 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67707671 / 100000000) ≤ -Real.log (250000000000 / 492028985507) ∧
    -Real.log (250000000000 / 492028985507) ≤ (677076711 / 1000000000) := by
  have h := checkLog_sound (w := (242028985507 / 742028985507)) (n := 12)
    (lo := (67707671 / 100000000)) (hi := (677076711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492028985507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492028985507 / 250000000000) = 1/(250000000000 / 492028985507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67707671 / 100000000) (677076711 / 1000000000) (Real.log (492028985507 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (492028985507 / 250000000000) = -Real.log (250000000000 / 492028985507) := by
    rw [show ((492028985507 / 250000000000) : ℝ) = ((250000000000 / 492028985507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (339194191 / 500000000) ≤ -Real.log (100000000000 / 197069915869) ∧
    -Real.log (100000000000 / 197069915869) ≤ (678388383 / 1000000000) := by
  have h := checkLog_sound (w := (97069915869 / 297069915869)) (n := 12)
    (lo := (339194191 / 500000000)) (hi := (678388383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197069915869 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197069915869 / 100000000000) = 1/(100000000000 / 197069915869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (339194191 / 500000000) (678388383 / 1000000000) (Real.log (197069915869 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (197069915869 / 100000000000) = -Real.log (100000000000 / 197069915869) := by
    rw [show ((197069915869 / 100000000000) : ℝ) = ((100000000000 / 197069915869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (471987233 / 1000000000) ≤ -Real.log (250000000000 / 400794229277) ∧
    -Real.log (250000000000 / 400794229277) ≤ (235993617 / 500000000) := by
  have h := checkLog_sound (w := (150794229277 / 650794229277)) (n := 12)
    (lo := (471987233 / 1000000000)) (hi := (235993617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400794229277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400794229277 / 250000000000) = 1/(250000000000 / 400794229277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (471987233 / 1000000000) (235993617 / 500000000) (Real.log (400794229277 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (400794229277 / 250000000000) = -Real.log (250000000000 / 400794229277) := by
    rw [show ((400794229277 / 250000000000) : ℝ) = ((250000000000 / 400794229277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (59109637 / 125000000) ≤ -Real.log (250000000000 / 401151039693) ∧
    -Real.log (250000000000 / 401151039693) ≤ (472877097 / 1000000000) := by
  have h := checkLog_sound (w := (151151039693 / 651151039693)) (n := 12)
    (lo := (59109637 / 125000000)) (hi := (472877097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401151039693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401151039693 / 250000000000) = 1/(250000000000 / 401151039693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (59109637 / 125000000) (472877097 / 1000000000) (Real.log (401151039693 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (401151039693 / 250000000000) = -Real.log (250000000000 / 401151039693) := by
    rw [show ((401151039693 / 250000000000) : ℝ) = ((250000000000 / 401151039693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (83937727 / 250000000) ≤ -Real.log (500000000000 / 699495252397) ∧
    -Real.log (500000000000 / 699495252397) ≤ (335750909 / 1000000000) := by
  have h := checkLog_sound (w := (199495252397 / 1199495252397)) (n := 12)
    (lo := (83937727 / 250000000)) (hi := (335750909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699495252397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699495252397 / 500000000000) = 1/(500000000000 / 699495252397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (83937727 / 250000000) (335750909 / 1000000000) (Real.log (699495252397 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (699495252397 / 500000000000) = -Real.log (500000000000 / 699495252397) := by
    rw [show ((699495252397 / 500000000000) : ℝ) = ((500000000000 / 699495252397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (168196347 / 500000000) ≤ -Real.log (62500000000 / 87493040323) ∧
    -Real.log (62500000000 / 87493040323) ≤ (67278539 / 200000000) := by
  have h := checkLog_sound (w := (24993040323 / 149993040323)) (n := 12)
    (lo := (168196347 / 500000000)) (hi := (67278539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87493040323 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87493040323 / 62500000000) = 1/(62500000000 / 87493040323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (168196347 / 500000000) (67278539 / 200000000) (Real.log (87493040323 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87493040323 / 62500000000) = -Real.log (62500000000 / 87493040323) := by
    rw [show ((87493040323 / 62500000000) : ℝ) = ((62500000000 / 87493040323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28157621 / 1000000000) ≤ -Real.log (60764694351 / 62500000000) ∧
    -Real.log (60764694351 / 62500000000) ≤ (14078811 / 500000000) := by
  have h := checkLog_sound (w := (1735305649 / 123264694351)) (n := 12)
    (lo := (28157621 / 1000000000)) (hi := (14078811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60764694351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60764694351) = 1/(60764694351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-14078811 / 500000000) (-28157621 / 1000000000) (Real.log (60764694351 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14025391 / 500000000) ≤ -Real.log (60771186759 / 62500000000) ∧
    -Real.log (60771186759 / 62500000000) ≤ (28050783 / 1000000000) := by
  have h := checkLog_sound (w := (1728813241 / 123271186759)) (n := 12)
    (lo := (14025391 / 500000000)) (hi := (28050783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60771186759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60771186759) = 1/(60771186759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28050783 / 1000000000) (-14025391 / 500000000) (Real.log (60771186759 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell130

end


