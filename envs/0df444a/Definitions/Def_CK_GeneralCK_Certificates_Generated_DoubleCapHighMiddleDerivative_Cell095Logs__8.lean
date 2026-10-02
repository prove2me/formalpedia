-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell095Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell095Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:57:54.026983+00:00
-- url     : https://prove2.me/theorems/33006714-2d00-4932-a4f6-71593c877c66
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell095Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell096…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell095Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell096Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell097Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell098Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell099Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell100Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell101Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell102Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell095Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell096Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell097Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell098Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell099Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell100Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell101Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell102Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell095Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell096Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell097Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell098Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell099Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell100Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell101Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell102Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell095Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell096Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell097Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell098Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell099Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell100Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell101Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell102Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell095Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell095
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

theorem reflection_log_1_neg : (66790109 / 250000000) ≤ -Real.log (160 / 209) ∧
    -Real.log (160 / 209) ≤ (267160437 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 369)) (n := 12)
    (lo := (66790109 / 250000000)) (hi := (267160437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209 / 160) = 1/(160 / 209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66790109 / 250000000) (267160437 / 1000000000) (Real.log (209 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (209 / 160) = -Real.log (160 / 209) := by
    rw [show ((209 / 160) : ℝ) = ((160 / 209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (365643613 / 1000000000) ≤ -Real.log (111 / 160) ∧
    -Real.log (111 / 160) ≤ (182821807 / 500000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 111) = 1/(111 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-182821807 / 500000000) (-365643613 / 1000000000) (Real.log (111 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266711771 / 1000000000) ≤ -Real.log (1024 / 1337) ∧
    -Real.log (1024 / 1337) ≤ (66677943 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2361)) (n := 12)
    (lo := (266711771 / 1000000000)) (hi := (66677943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 1024) = 1/(1024 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266711771 / 1000000000) (66677943 / 250000000) (Real.log (1337 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1337 / 1024) = -Real.log (1024 / 1337) := by
    rw [show ((1337 / 1024) : ℝ) = ((1024 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (583679 / 1600000) ≤ -Real.log (711 / 1024) ∧
    -Real.log (711 / 1024) ≤ (22799961 / 62500000) := by
  have h := checkLog_sound (w := (313 / 1735)) (n := 12)
    (lo := (583679 / 1600000)) (hi := (22799961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 711) = 1/(711 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22799961 / 62500000) (-583679 / 1600000) (Real.log (711 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98199337 / 500000000) ≤ -Real.log (250000 / 304253) ∧
    -Real.log (250000 / 304253) ≤ (7855947 / 40000000) := by
  have h := checkLog_sound (w := (54253 / 554253)) (n := 12)
    (lo := (98199337 / 500000000)) (hi := (7855947 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304253 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304253 / 250000) = 1/(250000 / 304253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98199337 / 500000000) (7855947 / 40000000) (Real.log (304253 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (304253 / 250000) = -Real.log (250000 / 304253) := by
    rw [show ((304253 / 250000) : ℝ) = ((250000 / 304253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (61159477 / 250000000) ≤ -Real.log (195747 / 250000) ∧
    -Real.log (195747 / 250000) ≤ (244637909 / 1000000000) := by
  have h := checkLog_sound (w := (54253 / 445747)) (n := 12)
    (lo := (61159477 / 250000000)) (hi := (244637909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195747) = 1/(195747 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-244637909 / 1000000000) (-61159477 / 250000000) (Real.log (195747 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196744543 / 1000000000) ≤ -Real.log (1000000 / 1217433) ∧
    -Real.log (1000000 / 1217433) ≤ (6148267 / 31250000) := by
  have h := checkLog_sound (w := (217433 / 2217433)) (n := 12)
    (lo := (196744543 / 1000000000)) (hi := (6148267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217433 / 1000000) = 1/(1000000 / 1217433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196744543 / 1000000000) (6148267 / 31250000) (Real.log (1217433 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217433 / 1000000) = -Real.log (1000000 / 1217433) := by
    rw [show ((1217433 / 1000000) : ℝ) = ((1000000 / 1217433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245175737 / 1000000000) ≤ -Real.log (782567 / 1000000) ∧
    -Real.log (782567 / 1000000) ≤ (122587869 / 500000000) := by
  have h := checkLog_sound (w := (217433 / 1782567)) (n := 12)
    (lo := (245175737 / 1000000000)) (hi := (122587869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782567) = 1/(782567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122587869 / 500000000) (-245175737 / 1000000000) (Real.log (782567 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72257921 / 500000000) ≤ -Real.log (25000 / 28887) ∧
    -Real.log (25000 / 28887) ≤ (144515843 / 1000000000) := by
  have h := checkLog_sound (w := (3887 / 53887)) (n := 12)
    (lo := (72257921 / 500000000)) (hi := (144515843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28887 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28887 / 25000) = 1/(25000 / 28887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72257921 / 500000000) (144515843 / 1000000000) (Real.log (28887 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (28887 / 25000) = -Real.log (25000 / 28887) := by
    rw [show ((28887 / 25000) : ℝ) = ((25000 / 28887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8449343 / 50000000) ≤ -Real.log (21113 / 25000) ∧
    -Real.log (21113 / 25000) ≤ (168986861 / 1000000000) := by
  have h := checkLog_sound (w := (3887 / 46113)) (n := 12)
    (lo := (8449343 / 50000000)) (hi := (168986861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21113) = 1/(21113 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168986861 / 1000000000) (-8449343 / 50000000) (Real.log (21113 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144783227 / 1000000000) ≤ -Real.log (1000000 / 1155789) ∧
    -Real.log (1000000 / 1155789) ≤ (36195807 / 250000000) := by
  have h := checkLog_sound (w := (155789 / 2155789)) (n := 12)
    (lo := (144783227 / 1000000000)) (hi := (36195807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155789 / 1000000) = 1/(1000000 / 1155789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144783227 / 1000000000) (36195807 / 250000000) (Real.log (1155789 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1155789 / 1000000) = -Real.log (1000000 / 1155789) := by
    rw [show ((1155789 / 1000000) : ℝ) = ((1000000 / 1155789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33870563 / 200000000) ≤ -Real.log (844211 / 1000000) ∧
    -Real.log (844211 / 1000000) ≤ (10584551 / 62500000) := by
  have h := checkLog_sound (w := (155789 / 1844211)) (n := 12)
    (lo := (33870563 / 200000000)) (hi := (10584551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844211) = 1/(844211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10584551 / 62500000) (-33870563 / 200000000) (Real.log (844211 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (631511147 / 1000000000) ≤ -Real.log (500000000000 / 940225035161) ∧
    -Real.log (500000000000 / 940225035161) ≤ (157877787 / 250000000) := by
  have h := checkLog_sound (w := (440225035161 / 1440225035161)) (n := 12)
    (lo := (631511147 / 1000000000)) (hi := (157877787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940225035161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940225035161 / 500000000000) = 1/(500000000000 / 940225035161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (631511147 / 1000000000) (157877787 / 250000000) (Real.log (940225035161 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (940225035161 / 500000000000) = -Real.log (500000000000 / 940225035161) := by
    rw [show ((940225035161 / 500000000000) : ℝ) = ((500000000000 / 940225035161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (12656081 / 20000000) ≤ -Real.log (250000000000 / 470720720721) ∧
    -Real.log (250000000000 / 470720720721) ≤ (632804051 / 1000000000) := by
  have h := checkLog_sound (w := (220720720721 / 720720720721)) (n := 12)
    (lo := (12656081 / 20000000)) (hi := (632804051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470720720721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470720720721 / 250000000000) = 1/(250000000000 / 470720720721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (12656081 / 20000000) (632804051 / 1000000000) (Real.log (470720720721 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (470720720721 / 250000000000) = -Real.log (250000000000 / 470720720721) := by
    rw [show ((470720720721 / 250000000000) : ℝ) = ((250000000000 / 470720720721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (441036583 / 1000000000) ≤ -Real.log (31250000000 / 48572423843) ∧
    -Real.log (31250000000 / 48572423843) ≤ (55129573 / 125000000) := by
  have h := checkLog_sound (w := (17322423843 / 79822423843)) (n := 12)
    (lo := (441036583 / 1000000000)) (hi := (55129573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48572423843 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48572423843 / 31250000000) = 1/(31250000000 / 48572423843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (441036583 / 1000000000) (55129573 / 125000000) (Real.log (48572423843 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48572423843 / 31250000000) = -Real.log (31250000000 / 48572423843) := by
    rw [show ((48572423843 / 31250000000) : ℝ) = ((31250000000 / 48572423843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11048007 / 25000000) ≤ -Real.log (250000000000 / 388922929283) ∧
    -Real.log (250000000000 / 388922929283) ≤ (441920281 / 1000000000) := by
  have h := checkLog_sound (w := (138922929283 / 638922929283)) (n := 12)
    (lo := (11048007 / 25000000)) (hi := (441920281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388922929283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388922929283 / 250000000000) = 1/(250000000000 / 388922929283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (11048007 / 25000000) (441920281 / 1000000000) (Real.log (388922929283 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (388922929283 / 250000000000) = -Real.log (250000000000 / 388922929283) := by
    rw [show ((388922929283 / 250000000000) : ℝ) = ((250000000000 / 388922929283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (156751351 / 500000000) ≤ -Real.log (125000000000 / 171026145029) ∧
    -Real.log (125000000000 / 171026145029) ≤ (313502703 / 1000000000) := by
  have h := checkLog_sound (w := (46026145029 / 296026145029)) (n := 12)
    (lo := (156751351 / 500000000)) (hi := (313502703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171026145029 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171026145029 / 125000000000) = 1/(125000000000 / 171026145029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (156751351 / 500000000) (313502703 / 1000000000) (Real.log (171026145029 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171026145029 / 125000000000) = -Real.log (125000000000 / 171026145029) := by
    rw [show ((171026145029 / 125000000000) : ℝ) = ((125000000000 / 171026145029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (314136043 / 1000000000) ≤ -Real.log (250000000000 / 342268994363) ∧
    -Real.log (250000000000 / 342268994363) ≤ (78534011 / 250000000) := by
  have h := checkLog_sound (w := (92268994363 / 592268994363)) (n := 12)
    (lo := (314136043 / 1000000000)) (hi := (78534011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342268994363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342268994363 / 250000000000) = 1/(250000000000 / 342268994363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (314136043 / 1000000000) (78534011 / 250000000) (Real.log (342268994363 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342268994363 / 250000000000) = -Real.log (250000000000 / 342268994363) := by
    rw [show ((342268994363 / 250000000000) : ℝ) = ((250000000000 / 342268994363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24569587 / 1000000000) ≤ -Real.log (975729787479 / 1000000000000) ∧
    -Real.log (975729787479 / 1000000000000) ≤ (6142397 / 250000000) := by
  have h := checkLog_sound (w := (24270212521 / 1975729787479)) (n := 12)
    (lo := (24569587 / 1000000000)) (hi := (6142397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975729787479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975729787479) = 1/(975729787479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6142397 / 250000000) (-24569587 / 1000000000) (Real.log (975729787479 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12235509 / 500000000) ≤ -Real.log (609891231 / 625000000) ∧
    -Real.log (609891231 / 625000000) ≤ (24471019 / 1000000000) := by
  have h := checkLog_sound (w := (15108769 / 1234891231)) (n := 12)
    (lo := (12235509 / 500000000)) (hi := (24471019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 609891231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 609891231) = 1/(609891231 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24471019 / 1000000000) (-12235509 / 500000000) (Real.log (609891231 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell095

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell096Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell096
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

theorem reflection_log_1_neg : (2676089 / 10000000) ≤ -Real.log (5120 / 6691) ∧
    -Real.log (5120 / 6691) ≤ (267608901 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 11811)) (n := 12)
    (lo := (2676089 / 10000000)) (hi := (267608901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6691 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6691 / 5120) = 1/(5120 / 6691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2676089 / 10000000) (267608901 / 1000000000) (Real.log (6691 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6691 / 5120) = -Real.log (5120 / 6691) := by
    rw [show ((6691 / 5120) : ℝ) = ((5120 / 6691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73297713 / 200000000) ≤ -Real.log (3549 / 5120) ∧
    -Real.log (3549 / 5120) ≤ (183244283 / 500000000) := by
  have h := checkLog_sound (w := (1571 / 8669)) (n := 12)
    (lo := (73297713 / 200000000)) (hi := (183244283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3549) = 1/(3549 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-183244283 / 500000000) (-73297713 / 200000000) (Real.log (3549 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66790109 / 250000000) ≤ -Real.log (160 / 209) ∧
    -Real.log (160 / 209) ≤ (267160437 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 369)) (n := 12)
    (lo := (66790109 / 250000000)) (hi := (267160437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209 / 160) = 1/(160 / 209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66790109 / 250000000) (267160437 / 1000000000) (Real.log (209 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (209 / 160) = -Real.log (160 / 209) := by
    rw [show ((209 / 160) : ℝ) = ((160 / 209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (365643613 / 1000000000) ≤ -Real.log (111 / 160) ∧
    -Real.log (111 / 160) ≤ (182821807 / 500000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 111) = 1/(111 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-182821807 / 500000000) (-365643613 / 1000000000) (Real.log (111 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98371861 / 500000000) ≤ -Real.log (125000 / 152179) ∧
    -Real.log (125000 / 152179) ≤ (196743723 / 1000000000) := by
  have h := checkLog_sound (w := (27179 / 277179)) (n := 12)
    (lo := (98371861 / 500000000)) (hi := (196743723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152179 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152179 / 125000) = 1/(125000 / 152179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98371861 / 500000000) (196743723 / 1000000000) (Real.log (152179 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (152179 / 125000) = -Real.log (125000 / 152179) := by
    rw [show ((152179 / 125000) : ℝ) = ((125000 / 152179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245174459 / 1000000000) ≤ -Real.log (97821 / 125000) ∧
    -Real.log (97821 / 125000) ≤ (12258723 / 50000000) := by
  have h := checkLog_sound (w := (27179 / 222821)) (n := 12)
    (lo := (245174459 / 1000000000)) (hi := (12258723 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97821) = 1/(97821 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12258723 / 50000000) (-245174459 / 1000000000) (Real.log (97821 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197088651 / 1000000000) ≤ -Real.log (250000 / 304463) ∧
    -Real.log (250000 / 304463) ≤ (49272163 / 250000000) := by
  have h := checkLog_sound (w := (54463 / 554463)) (n := 12)
    (lo := (197088651 / 1000000000)) (hi := (49272163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304463 / 250000) = 1/(250000 / 304463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197088651 / 1000000000) (49272163 / 250000000) (Real.log (304463 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (304463 / 250000) = -Real.log (250000 / 304463) := by
    rw [show ((304463 / 250000) : ℝ) = ((250000 / 304463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122855649 / 500000000) ≤ -Real.log (195537 / 250000) ∧
    -Real.log (195537 / 250000) ≤ (245711299 / 1000000000) := by
  have h := checkLog_sound (w := (54463 / 445537)) (n := 12)
    (lo := (122855649 / 500000000)) (hi := (245711299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195537) = 1/(195537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-245711299 / 1000000000) (-122855649 / 500000000) (Real.log (195537 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72391181 / 500000000) ≤ -Real.log (250000 / 288947) ∧
    -Real.log (250000 / 288947) ≤ (144782363 / 1000000000) := by
  have h := checkLog_sound (w := (38947 / 538947)) (n := 12)
    (lo := (72391181 / 500000000)) (hi := (144782363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288947 / 250000) = 1/(250000 / 288947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72391181 / 500000000) (144782363 / 1000000000) (Real.log (288947 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (288947 / 250000) = -Real.log (250000 / 288947) := by
    rw [show ((288947 / 250000) : ℝ) = ((250000 / 288947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (169351631 / 1000000000) ≤ -Real.log (211053 / 250000) ∧
    -Real.log (211053 / 250000) ≤ (10584477 / 62500000) := by
  have h := checkLog_sound (w := (38947 / 461053)) (n := 12)
    (lo := (169351631 / 1000000000)) (hi := (10584477 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211053) = 1/(211053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10584477 / 62500000) (-169351631 / 1000000000) (Real.log (211053 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145050541 / 1000000000) ≤ -Real.log (500000 / 578049) ∧
    -Real.log (500000 / 578049) ≤ (72525271 / 500000000) := by
  have h := checkLog_sound (w := (78049 / 1078049)) (n := 12)
    (lo := (145050541 / 1000000000)) (hi := (72525271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578049 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578049 / 500000) = 1/(500000 / 578049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145050541 / 1000000000) (72525271 / 500000000) (Real.log (578049 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (578049 / 500000) = -Real.log (500000 / 578049) := by
    rw [show ((578049 / 500000) : ℝ) = ((500000 / 578049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21214863 / 125000000) ≤ -Real.log (421951 / 500000) ∧
    -Real.log (421951 / 500000) ≤ (33943781 / 200000000) := by
  have h := checkLog_sound (w := (78049 / 921951)) (n := 12)
    (lo := (21214863 / 125000000)) (hi := (33943781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421951) = 1/(421951 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33943781 / 200000000) (-21214863 / 125000000) (Real.log (421951 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12656081 / 20000000) ≤ -Real.log (500000000000 / 941441441441) ∧
    -Real.log (500000000000 / 941441441441) ≤ (632804051 / 1000000000) := by
  have h := checkLog_sound (w := (441441441441 / 1441441441441)) (n := 12)
    (lo := (12656081 / 20000000)) (hi := (632804051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941441441441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941441441441 / 500000000000) = 1/(500000000000 / 941441441441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12656081 / 20000000) (632804051 / 1000000000) (Real.log (941441441441 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (941441441441 / 500000000000) = -Real.log (500000000000 / 941441441441) := by
    rw [show ((941441441441 / 500000000000) : ℝ) = ((500000000000 / 941441441441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (317048733 / 500000000) ≤ -Real.log (500000000000 / 942659904199) ∧
    -Real.log (500000000000 / 942659904199) ≤ (634097467 / 1000000000) := by
  have h := checkLog_sound (w := (442659904199 / 1442659904199)) (n := 12)
    (lo := (317048733 / 500000000)) (hi := (634097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((942659904199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(942659904199 / 500000000000) = 1/(500000000000 / 942659904199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (317048733 / 500000000) (634097467 / 1000000000) (Real.log (942659904199 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (942659904199 / 500000000000) = -Real.log (500000000000 / 942659904199) := by
    rw [show ((942659904199 / 500000000000) : ℝ) = ((500000000000 / 942659904199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (441918181 / 1000000000) ≤ -Real.log (500000000000 / 777844225677) ∧
    -Real.log (500000000000 / 777844225677) ≤ (220959091 / 500000000) := by
  have h := checkLog_sound (w := (277844225677 / 1277844225677)) (n := 12)
    (lo := (441918181 / 1000000000)) (hi := (220959091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777844225677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777844225677 / 500000000000) = 1/(500000000000 / 777844225677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (441918181 / 1000000000) (220959091 / 500000000) (Real.log (777844225677 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (777844225677 / 500000000000) = -Real.log (500000000000 / 777844225677) := by
    rw [show ((777844225677 / 500000000000) : ℝ) = ((500000000000 / 777844225677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (442799949 / 1000000000) ≤ -Real.log (500000000000 / 778530406011) ∧
    -Real.log (500000000000 / 778530406011) ≤ (8855999 / 20000000) := by
  have h := checkLog_sound (w := (278530406011 / 1278530406011)) (n := 12)
    (lo := (442799949 / 1000000000)) (hi := (8855999 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778530406011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(778530406011 / 500000000000) = 1/(500000000000 / 778530406011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (442799949 / 1000000000) (8855999 / 20000000) (Real.log (778530406011 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (778530406011 / 500000000000) = -Real.log (500000000000 / 778530406011) := by
    rw [show ((778530406011 / 500000000000) : ℝ) = ((500000000000 / 778530406011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (314133993 / 1000000000) ≤ -Real.log (125000000000 / 171134146399) ∧
    -Real.log (125000000000 / 171134146399) ≤ (157066997 / 500000000) := by
  have h := checkLog_sound (w := (46134146399 / 296134146399)) (n := 12)
    (lo := (314133993 / 1000000000)) (hi := (157066997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171134146399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171134146399 / 125000000000) = 1/(125000000000 / 171134146399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (314133993 / 1000000000) (157066997 / 500000000) (Real.log (171134146399 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171134146399 / 125000000000) = -Real.log (125000000000 / 171134146399) := by
    rw [show ((171134146399 / 125000000000) : ℝ) = ((125000000000 / 171134146399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (157384723 / 500000000) ≤ -Real.log (250000000000 / 342485857363) ∧
    -Real.log (250000000000 / 342485857363) ≤ (314769447 / 1000000000) := by
  have h := checkLog_sound (w := (92485857363 / 592485857363)) (n := 12)
    (lo := (157384723 / 500000000)) (hi := (314769447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342485857363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342485857363 / 250000000000) = 1/(250000000000 / 342485857363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (157384723 / 500000000) (314769447 / 1000000000) (Real.log (342485857363 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342485857363 / 250000000000) = -Real.log (250000000000 / 342485857363) := by
    rw [show ((342485857363 / 250000000000) : ℝ) = ((250000000000 / 342485857363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24668363 / 1000000000) ≤ -Real.log (243908353599 / 250000000000) ∧
    -Real.log (243908353599 / 250000000000) ≤ (6167091 / 250000000) := by
  have h := checkLog_sound (w := (6091646401 / 493908353599)) (n := 12)
    (lo := (24668363 / 1000000000)) (hi := (6167091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243908353599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243908353599) = 1/(243908353599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6167091 / 250000000) (-24668363 / 1000000000) (Real.log (243908353599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6142317 / 250000000) ≤ -Real.log (60983131191 / 62500000000) ∧
    -Real.log (60983131191 / 62500000000) ≤ (24569269 / 1000000000) := by
  have h := checkLog_sound (w := (1516868809 / 123483131191)) (n := 12)
    (lo := (6142317 / 250000000)) (hi := (24569269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60983131191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60983131191) = 1/(60983131191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24569269 / 1000000000) (-6142317 / 250000000) (Real.log (60983131191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell096

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell097Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell097
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

theorem reflection_log_1_neg : (268057163 / 1000000000) ≤ -Real.log (2560 / 3347) ∧
    -Real.log (2560 / 3347) ≤ (67014291 / 250000000) := by
  have h := checkLog_sound (w := (787 / 5907)) (n := 12)
    (lo := (268057163 / 1000000000)) (hi := (67014291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3347 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3347 / 2560) = 1/(2560 / 3347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (268057163 / 1000000000) (67014291 / 250000000) (Real.log (3347 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3347 / 2560) = -Real.log (2560 / 3347) := by
    rw [show ((3347 / 2560) : ℝ) = ((2560 / 3347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (367334231 / 1000000000) ≤ -Real.log (1773 / 2560) ∧
    -Real.log (1773 / 2560) ≤ (45916779 / 125000000) := by
  have h := checkLog_sound (w := (787 / 4333)) (n := 12)
    (lo := (367334231 / 1000000000)) (hi := (45916779 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1773) = 1/(1773 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45916779 / 125000000) (-367334231 / 1000000000) (Real.log (1773 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2676089 / 10000000) ≤ -Real.log (5120 / 6691) ∧
    -Real.log (5120 / 6691) ≤ (267608901 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 11811)) (n := 12)
    (lo := (2676089 / 10000000)) (hi := (267608901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6691 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6691 / 5120) = 1/(5120 / 6691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2676089 / 10000000) (267608901 / 1000000000) (Real.log (6691 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6691 / 5120) = -Real.log (5120 / 6691) := by
    rw [show ((6691 / 5120) : ℝ) = ((5120 / 6691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73297713 / 200000000) ≤ -Real.log (3549 / 5120) ∧
    -Real.log (3549 / 5120) ≤ (183244283 / 500000000) := by
  have h := checkLog_sound (w := (1571 / 8669)) (n := 12)
    (lo := (73297713 / 200000000)) (hi := (183244283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3549) = 1/(3549 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-183244283 / 500000000) (-73297713 / 200000000) (Real.log (3549 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19708783 / 100000000) ≤ -Real.log (1000000 / 1217851) ∧
    -Real.log (1000000 / 1217851) ≤ (197087831 / 1000000000) := by
  have h := checkLog_sound (w := (217851 / 2217851)) (n := 12)
    (lo := (19708783 / 100000000)) (hi := (197087831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217851 / 1000000) = 1/(1000000 / 1217851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19708783 / 100000000) (197087831 / 1000000000) (Real.log (1217851 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1217851 / 1000000) = -Real.log (1000000 / 1217851) := by
    rw [show ((1217851 / 1000000) : ℝ) = ((1000000 / 1217851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245710019 / 1000000000) ≤ -Real.log (782149 / 1000000) ∧
    -Real.log (782149 / 1000000) ≤ (12285501 / 50000000) := by
  have h := checkLog_sound (w := (217851 / 1782149)) (n := 12)
    (lo := (245710019 / 1000000000)) (hi := (12285501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782149) = 1/(782149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12285501 / 50000000) (-245710019 / 1000000000) (Real.log (782149 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197433461 / 1000000000) ≤ -Real.log (31250 / 38071) ∧
    -Real.log (31250 / 38071) ≤ (98716731 / 500000000) := by
  have h := checkLog_sound (w := (6821 / 69321)) (n := 12)
    (lo := (197433461 / 1000000000)) (hi := (98716731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38071 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38071 / 31250) = 1/(31250 / 38071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197433461 / 1000000000) (98716731 / 500000000) (Real.log (38071 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (38071 / 31250) = -Real.log (31250 / 38071) := by
    rw [show ((38071 / 31250) : ℝ) = ((31250 / 38071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9849937 / 40000000) ≤ -Real.log (24429 / 31250) ∧
    -Real.log (24429 / 31250) ≤ (123124213 / 500000000) := by
  have h := checkLog_sound (w := (6821 / 55679)) (n := 12)
    (lo := (9849937 / 40000000)) (hi := (123124213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24429) = 1/(24429 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-123124213 / 500000000) (-9849937 / 40000000) (Real.log (24429 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36262419 / 250000000) ≤ -Real.log (1000000 / 1156097) ∧
    -Real.log (1000000 / 1156097) ≤ (145049677 / 1000000000) := by
  have h := checkLog_sound (w := (156097 / 2156097)) (n := 12)
    (lo := (36262419 / 250000000)) (hi := (145049677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156097 / 1000000) = 1/(1000000 / 1156097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36262419 / 250000000) (145049677 / 1000000000) (Real.log (1156097 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1156097 / 1000000) = -Real.log (1000000 / 1156097) := by
    rw [show ((1156097 / 1000000) : ℝ) = ((1000000 / 1156097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (169717719 / 1000000000) ≤ -Real.log (843903 / 1000000) ∧
    -Real.log (843903 / 1000000) ≤ (4242943 / 25000000) := by
  have h := checkLog_sound (w := (156097 / 1843903)) (n := 12)
    (lo := (169717719 / 1000000000)) (hi := (4242943 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843903) = 1/(843903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4242943 / 25000000) (-169717719 / 1000000000) (Real.log (843903 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18164723 / 125000000) ≤ -Real.log (1000000 / 1156407) ∧
    -Real.log (1000000 / 1156407) ≤ (29063557 / 200000000) := by
  have h := checkLog_sound (w := (156407 / 2156407)) (n := 12)
    (lo := (18164723 / 125000000)) (hi := (29063557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156407 / 1000000) = 1/(1000000 / 1156407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18164723 / 125000000) (29063557 / 200000000) (Real.log (1156407 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1156407 / 1000000) = -Real.log (1000000 / 1156407) := by
    rw [show ((1156407 / 1000000) : ℝ) = ((1000000 / 1156407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21260641 / 125000000) ≤ -Real.log (843593 / 1000000) ∧
    -Real.log (843593 / 1000000) ≤ (170085129 / 1000000000) := by
  have h := checkLog_sound (w := (156407 / 1843593)) (n := 12)
    (lo := (21260641 / 125000000)) (hi := (170085129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843593) = 1/(843593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170085129 / 1000000000) (-21260641 / 125000000) (Real.log (843593 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (317048733 / 500000000) ≤ -Real.log (250000000000 / 471329952099) ∧
    -Real.log (250000000000 / 471329952099) ≤ (634097467 / 1000000000) := by
  have h := checkLog_sound (w := (221329952099 / 721329952099)) (n := 12)
    (lo := (317048733 / 500000000)) (hi := (634097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471329952099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471329952099 / 250000000000) = 1/(250000000000 / 471329952099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (317048733 / 500000000) (634097467 / 1000000000) (Real.log (471329952099 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (471329952099 / 250000000000) = -Real.log (250000000000 / 471329952099) := by
    rw [show ((471329952099 / 250000000000) : ℝ) = ((250000000000 / 471329952099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (127078279 / 200000000) ≤ -Real.log (500000000000 / 943880428653) ∧
    -Real.log (500000000000 / 943880428653) ≤ (158847849 / 250000000) := by
  have h := checkLog_sound (w := (443880428653 / 1443880428653)) (n := 12)
    (lo := (127078279 / 200000000)) (hi := (158847849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943880428653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943880428653 / 500000000000) = 1/(500000000000 / 943880428653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (127078279 / 200000000) (158847849 / 250000000) (Real.log (943880428653 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (943880428653 / 500000000000) = -Real.log (500000000000 / 943880428653) := by
    rw [show ((943880428653 / 500000000000) : ℝ) = ((500000000000 / 943880428653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (442797849 / 1000000000) ≤ -Real.log (125000000000 / 194632192843) ∧
    -Real.log (125000000000 / 194632192843) ≤ (8855957 / 20000000) := by
  have h := checkLog_sound (w := (69632192843 / 319632192843)) (n := 12)
    (lo := (442797849 / 1000000000)) (hi := (8855957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194632192843 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194632192843 / 125000000000) = 1/(125000000000 / 194632192843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (442797849 / 1000000000) (8855957 / 20000000) (Real.log (194632192843 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (194632192843 / 125000000000) = -Real.log (125000000000 / 194632192843) := by
    rw [show ((194632192843 / 125000000000) : ℝ) = ((125000000000 / 194632192843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (221840943 / 500000000) ≤ -Real.log (500000000000 / 779217323673) ∧
    -Real.log (500000000000 / 779217323673) ≤ (443681887 / 1000000000) := by
  have h := checkLog_sound (w := (279217323673 / 1279217323673)) (n := 12)
    (lo := (221840943 / 500000000)) (hi := (443681887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779217323673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779217323673 / 500000000000) = 1/(500000000000 / 779217323673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (221840943 / 500000000) (443681887 / 1000000000) (Real.log (779217323673 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (779217323673 / 500000000000) = -Real.log (500000000000 / 779217323673) := by
    rw [show ((779217323673 / 500000000000) : ℝ) = ((500000000000 / 779217323673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (78691849 / 250000000) ≤ -Real.log (62500000000 / 85621288821) ∧
    -Real.log (62500000000 / 85621288821) ≤ (314767397 / 1000000000) := by
  have h := checkLog_sound (w := (23121288821 / 148121288821)) (n := 12)
    (lo := (78691849 / 250000000)) (hi := (314767397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85621288821 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85621288821 / 62500000000) = 1/(62500000000 / 85621288821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78691849 / 250000000) (314767397 / 1000000000) (Real.log (85621288821 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (85621288821 / 62500000000) = -Real.log (62500000000 / 85621288821) := by
    rw [show ((85621288821 / 62500000000) : ℝ) = ((62500000000 / 85621288821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9856341 / 31250000) ≤ -Real.log (100000000000 / 137081151693) ∧
    -Real.log (100000000000 / 137081151693) ≤ (315402913 / 1000000000) := by
  have h := checkLog_sound (w := (37081151693 / 237081151693)) (n := 12)
    (lo := (9856341 / 31250000)) (hi := (315402913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137081151693 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137081151693 / 100000000000) = 1/(100000000000 / 137081151693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9856341 / 31250000) (315402913 / 1000000000) (Real.log (137081151693 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137081151693 / 100000000000) = -Real.log (100000000000 / 137081151693) := by
    rw [show ((137081151693 / 100000000000) : ℝ) = ((100000000000 / 137081151693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24767343 / 1000000000) ≤ -Real.log (975536850351 / 1000000000000) ∧
    -Real.log (975536850351 / 1000000000000) ≤ (1547959 / 62500000) := by
  have h := checkLog_sound (w := (24463149649 / 1975536850351)) (n := 12)
    (lo := (24767343 / 1000000000)) (hi := (1547959 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975536850351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975536850351) = 1/(975536850351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1547959 / 62500000) (-24767343 / 1000000000) (Real.log (975536850351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24668043 / 1000000000) ≤ -Real.log (975633726591 / 1000000000000) ∧
    -Real.log (975633726591 / 1000000000000) ≤ (6167011 / 250000000) := by
  have h := checkLog_sound (w := (24366273409 / 1975633726591)) (n := 12)
    (lo := (24668043 / 1000000000)) (hi := (6167011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975633726591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975633726591) = 1/(975633726591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6167011 / 250000000) (-24668043 / 1000000000) (Real.log (975633726591 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell097

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell098Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell098
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

theorem reflection_log_1_neg : (10740209 / 40000000) ≤ -Real.log (5120 / 6697) ∧
    -Real.log (5120 / 6697) ≤ (134252613 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 11817)) (n := 12)
    (lo := (10740209 / 40000000)) (hi := (134252613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6697 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6697 / 5120) = 1/(5120 / 6697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10740209 / 40000000) (134252613 / 500000000) (Real.log (6697 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6697 / 5120) = -Real.log (5120 / 6697) := by
    rw [show ((6697 / 5120) : ℝ) = ((5120 / 6697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (368180613 / 1000000000) ≤ -Real.log (3543 / 5120) ∧
    -Real.log (3543 / 5120) ≤ (184090307 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 8663)) (n := 12)
    (lo := (368180613 / 1000000000)) (hi := (184090307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3543) = 1/(3543 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-184090307 / 500000000) (-368180613 / 1000000000) (Real.log (3543 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (268057163 / 1000000000) ≤ -Real.log (2560 / 3347) ∧
    -Real.log (2560 / 3347) ≤ (67014291 / 250000000) := by
  have h := checkLog_sound (w := (787 / 5907)) (n := 12)
    (lo := (268057163 / 1000000000)) (hi := (67014291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3347 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3347 / 2560) = 1/(2560 / 3347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (268057163 / 1000000000) (67014291 / 250000000) (Real.log (3347 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3347 / 2560) = -Real.log (2560 / 3347) := by
    rw [show ((3347 / 2560) : ℝ) = ((2560 / 3347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (367334231 / 1000000000) ≤ -Real.log (1773 / 2560) ∧
    -Real.log (1773 / 2560) ≤ (45916779 / 125000000) := by
  have h := checkLog_sound (w := (787 / 4333)) (n := 12)
    (lo := (367334231 / 1000000000)) (hi := (45916779 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1773) = 1/(1773 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45916779 / 125000000) (-367334231 / 1000000000) (Real.log (1773 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616977 / 3125000) ≤ -Real.log (1000000 / 1218271) ∧
    -Real.log (1000000 / 1218271) ≤ (197432641 / 1000000000) := by
  have h := checkLog_sound (w := (218271 / 2218271)) (n := 12)
    (lo := (616977 / 3125000)) (hi := (197432641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218271 / 1000000) = 1/(1000000 / 1218271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616977 / 3125000) (197432641 / 1000000000) (Real.log (1218271 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1218271 / 1000000) = -Real.log (1000000 / 1218271) := by
    rw [show ((1218271 / 1000000) : ℝ) = ((1000000 / 1218271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (49249429 / 200000000) ≤ -Real.log (781729 / 1000000) ∧
    -Real.log (781729 / 1000000) ≤ (123123573 / 500000000) := by
  have h := checkLog_sound (w := (218271 / 1781729)) (n := 12)
    (lo := (49249429 / 200000000)) (hi := (123123573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781729) = 1/(781729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-123123573 / 500000000) (-49249429 / 200000000) (Real.log (781729 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197777331 / 1000000000) ≤ -Real.log (1000000 / 1218691) ∧
    -Real.log (1000000 / 1218691) ≤ (49444333 / 250000000) := by
  have h := checkLog_sound (w := (218691 / 2218691)) (n := 12)
    (lo := (197777331 / 1000000000)) (hi := (49444333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218691 / 1000000) = 1/(1000000 / 1218691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197777331 / 1000000000) (49444333 / 250000000) (Real.log (1218691 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1218691 / 1000000) = -Real.log (1000000 / 1218691) := by
    rw [show ((1218691 / 1000000) : ℝ) = ((1000000 / 1218691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3084807 / 12500000) ≤ -Real.log (781309 / 1000000) ∧
    -Real.log (781309 / 1000000) ≤ (246784561 / 1000000000) := by
  have h := checkLog_sound (w := (218691 / 1781309)) (n := 12)
    (lo := (3084807 / 12500000)) (hi := (246784561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781309) = 1/(781309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-246784561 / 1000000000) (-3084807 / 12500000) (Real.log (781309 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145316919 / 1000000000) ≤ -Real.log (500000 / 578203) ∧
    -Real.log (500000 / 578203) ≤ (3632923 / 25000000) := by
  have h := checkLog_sound (w := (78203 / 1078203)) (n := 12)
    (lo := (145316919 / 1000000000)) (hi := (3632923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578203 / 500000) = 1/(500000 / 578203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145316919 / 1000000000) (3632923 / 25000000) (Real.log (578203 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (578203 / 500000) = -Real.log (500000 / 578203) := by
    rw [show ((578203 / 500000) : ℝ) = ((500000 / 578203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (85041971 / 500000000) ≤ -Real.log (421797 / 500000) ∧
    -Real.log (421797 / 500000) ≤ (170083943 / 1000000000) := by
  have h := checkLog_sound (w := (78203 / 921797)) (n := 12)
    (lo := (85041971 / 500000000)) (hi := (170083943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421797) = 1/(421797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170083943 / 1000000000) (-85041971 / 500000000) (Real.log (421797 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145584091 / 1000000000) ≤ -Real.log (200000 / 231343) ∧
    -Real.log (200000 / 231343) ≤ (36396023 / 250000000) := by
  have h := checkLog_sound (w := (31343 / 431343)) (n := 12)
    (lo := (145584091 / 1000000000)) (hi := (36396023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231343 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231343 / 200000) = 1/(200000 / 231343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145584091 / 1000000000) (36396023 / 250000000) (Real.log (231343 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (231343 / 200000) = -Real.log (200000 / 231343) := by
    rw [show ((231343 / 200000) : ℝ) = ((200000 / 231343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170450299 / 1000000000) ≤ -Real.log (168657 / 200000) ∧
    -Real.log (168657 / 200000) ≤ (1704503 / 10000000) := by
  have h := checkLog_sound (w := (31343 / 368657)) (n := 12)
    (lo := (170450299 / 1000000000)) (hi := (1704503 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168657) = 1/(168657 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1704503 / 10000000) (-170450299 / 1000000000) (Real.log (168657 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (127078279 / 200000000) ≤ -Real.log (125000000000 / 235970107163) ∧
    -Real.log (125000000000 / 235970107163) ≤ (158847849 / 250000000) := by
  have h := checkLog_sound (w := (110970107163 / 360970107163)) (n := 12)
    (lo := (127078279 / 200000000)) (hi := (158847849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235970107163 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235970107163 / 125000000000) = 1/(125000000000 / 235970107163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (127078279 / 200000000) (158847849 / 250000000) (Real.log (235970107163 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (235970107163 / 125000000000) = -Real.log (125000000000 / 235970107163) := by
    rw [show ((235970107163 / 125000000000) : ℝ) = ((125000000000 / 235970107163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (636685839 / 1000000000) ≤ -Real.log (12500000000 / 23627575501) ∧
    -Real.log (12500000000 / 23627575501) ≤ (7958573 / 12500000) := by
  have h := checkLog_sound (w := (11127575501 / 36127575501)) (n := 12)
    (lo := (636685839 / 1000000000)) (hi := (7958573 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23627575501 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23627575501 / 12500000000) = 1/(12500000000 / 23627575501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (636685839 / 1000000000) (7958573 / 12500000) (Real.log (23627575501 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (23627575501 / 12500000000) = -Real.log (12500000000 / 23627575501) := by
    rw [show ((23627575501 / 12500000000) : ℝ) = ((12500000000 / 23627575501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (221839893 / 500000000) ≤ -Real.log (500000000000 / 779215687277) ∧
    -Real.log (500000000000 / 779215687277) ≤ (443679787 / 1000000000) := by
  have h := checkLog_sound (w := (279215687277 / 1279215687277)) (n := 12)
    (lo := (221839893 / 500000000)) (hi := (443679787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779215687277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779215687277 / 500000000000) = 1/(500000000000 / 779215687277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221839893 / 500000000) (443679787 / 1000000000) (Real.log (779215687277 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (779215687277 / 500000000000) = -Real.log (500000000000 / 779215687277) := by
    rw [show ((779215687277 / 500000000000) : ℝ) = ((500000000000 / 779215687277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (111140473 / 250000000) ≤ -Real.log (5000000000 / 7799033417) ∧
    -Real.log (5000000000 / 7799033417) ≤ (444561893 / 1000000000) := by
  have h := checkLog_sound (w := (2799033417 / 12799033417)) (n := 12)
    (lo := (111140473 / 250000000)) (hi := (444561893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7799033417 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7799033417 / 5000000000) = 1/(5000000000 / 7799033417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (111140473 / 250000000) (444561893 / 1000000000) (Real.log (7799033417 / 5000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (7799033417 / 5000000000) = -Real.log (5000000000 / 7799033417) := by
    rw [show ((7799033417 / 5000000000) : ℝ) = ((5000000000 / 7799033417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (157700431 / 500000000) ≤ -Real.log (250000000000 / 342702176639) ∧
    -Real.log (250000000000 / 342702176639) ≤ (315400863 / 1000000000) := by
  have h := checkLog_sound (w := (92702176639 / 592702176639)) (n := 12)
    (lo := (157700431 / 500000000)) (hi := (315400863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342702176639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342702176639 / 250000000000) = 1/(250000000000 / 342702176639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (157700431 / 500000000) (315400863 / 1000000000) (Real.log (342702176639 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (342702176639 / 250000000000) = -Real.log (250000000000 / 342702176639) := by
    rw [show ((342702176639 / 250000000000) : ℝ) = ((250000000000 / 342702176639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (31603439 / 100000000) ≤ -Real.log (500000000000 / 685838714077) ∧
    -Real.log (500000000000 / 685838714077) ≤ (316034391 / 1000000000) := by
  have h := checkLog_sound (w := (185838714077 / 1185838714077)) (n := 12)
    (lo := (31603439 / 100000000)) (hi := (316034391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685838714077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685838714077 / 500000000000) = 1/(500000000000 / 685838714077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (31603439 / 100000000) (316034391 / 1000000000) (Real.log (685838714077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (685838714077 / 500000000000) = -Real.log (500000000000 / 685838714077) := by
    rw [show ((685838714077 / 500000000000) : ℝ) = ((500000000000 / 685838714077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (777069 / 31250000) ≤ -Real.log (39017616351 / 40000000000) ∧
    -Real.log (39017616351 / 40000000000) ≤ (24866209 / 1000000000) := by
  have h := checkLog_sound (w := (982383649 / 79017616351)) (n := 12)
    (lo := (777069 / 31250000)) (hi := (24866209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39017616351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39017616351) = 1/(39017616351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24866209 / 1000000000) (-777069 / 31250000) (Real.log (39017616351 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24767023 / 1000000000) ≤ -Real.log (243884290791 / 250000000000) ∧
    -Real.log (243884290791 / 250000000000) ≤ (1547939 / 62500000) := by
  have h := checkLog_sound (w := (6115709209 / 493884290791)) (n := 12)
    (lo := (24767023 / 1000000000)) (hi := (1547939 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243884290791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243884290791) = 1/(243884290791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1547939 / 62500000) (-24767023 / 1000000000) (Real.log (243884290791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell098

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell099Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell099
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

theorem reflection_log_1_neg : (268953087 / 1000000000) ≤ -Real.log (256 / 335) ∧
    -Real.log (256 / 335) ≤ (525299 / 1953125) := by
  have h := checkLog_sound (w := (79 / 591)) (n := 12)
    (lo := (268953087 / 1000000000)) (hi := (525299 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335 / 256) = 1/(256 / 335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (268953087 / 1000000000) (525299 / 1953125) (Real.log (335 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (335 / 256) = -Real.log (256 / 335) := by
    rw [show ((335 / 256) : ℝ) = ((256 / 335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (369027711 / 1000000000) ≤ -Real.log (177 / 256) ∧
    -Real.log (177 / 256) ≤ (2883029 / 7812500) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 177) = 1/(177 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2883029 / 7812500) (-369027711 / 1000000000) (Real.log (177 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10740209 / 40000000) ≤ -Real.log (5120 / 6697) ∧
    -Real.log (5120 / 6697) ≤ (134252613 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 11817)) (n := 12)
    (lo := (10740209 / 40000000)) (hi := (134252613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6697 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6697 / 5120) = 1/(5120 / 6697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10740209 / 40000000) (134252613 / 500000000) (Real.log (6697 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6697 / 5120) = -Real.log (5120 / 6697) := by
    rw [show ((6697 / 5120) : ℝ) = ((5120 / 6697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (368180613 / 1000000000) ≤ -Real.log (3543 / 5120) ∧
    -Real.log (3543 / 5120) ≤ (184090307 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 8663)) (n := 12)
    (lo := (368180613 / 1000000000)) (hi := (184090307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3543) = 1/(3543 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-184090307 / 500000000) (-368180613 / 1000000000) (Real.log (3543 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (197776511 / 1000000000) ≤ -Real.log (100000 / 121869) ∧
    -Real.log (100000 / 121869) ≤ (1545129 / 7812500) := by
  have h := checkLog_sound (w := (21869 / 221869)) (n := 12)
    (lo := (197776511 / 1000000000)) (hi := (1545129 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121869 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121869 / 100000) = 1/(100000 / 121869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (197776511 / 1000000000) (1545129 / 7812500) (Real.log (121869 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121869 / 100000) = -Real.log (100000 / 121869) := by
    rw [show ((121869 / 100000) : ℝ) = ((100000 / 121869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3084791 / 12500000) ≤ -Real.log (78131 / 100000) ∧
    -Real.log (78131 / 100000) ≤ (246783281 / 1000000000) := by
  have h := checkLog_sound (w := (21869 / 178131)) (n := 12)
    (lo := (3084791 / 12500000)) (hi := (246783281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78131) = 1/(78131 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-246783281 / 1000000000) (-3084791 / 12500000) (Real.log (78131 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12382619 / 62500000) ≤ -Real.log (1000000 / 1219111) ∧
    -Real.log (1000000 / 1219111) ≤ (39624381 / 200000000) := by
  have h := checkLog_sound (w := (219111 / 2219111)) (n := 12)
    (lo := (12382619 / 62500000)) (hi := (39624381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219111 / 1000000) = 1/(1000000 / 1219111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12382619 / 62500000) (39624381 / 200000000) (Real.log (1219111 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1219111 / 1000000) = -Real.log (1000000 / 1219111) := by
    rw [show ((1219111 / 1000000) : ℝ) = ((1000000 / 1219111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30915283 / 125000000) ≤ -Real.log (780889 / 1000000) ∧
    -Real.log (780889 / 1000000) ≤ (49464453 / 200000000) := by
  have h := checkLog_sound (w := (219111 / 1780889)) (n := 12)
    (lo := (30915283 / 125000000)) (hi := (49464453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780889) = 1/(780889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-49464453 / 200000000) (-30915283 / 125000000) (Real.log (780889 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72791613 / 500000000) ≤ -Real.log (500000 / 578357) ∧
    -Real.log (500000 / 578357) ≤ (145583227 / 1000000000) := by
  have h := checkLog_sound (w := (78357 / 1078357)) (n := 12)
    (lo := (72791613 / 500000000)) (hi := (145583227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578357 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578357 / 500000) = 1/(500000 / 578357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72791613 / 500000000) (145583227 / 1000000000) (Real.log (578357 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (578357 / 500000) = -Real.log (500000 / 578357) := by
    rw [show ((578357 / 500000) : ℝ) = ((500000 / 578357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170449113 / 1000000000) ≤ -Real.log (421643 / 500000) ∧
    -Real.log (421643 / 500000) ≤ (85224557 / 500000000) := by
  have h := checkLog_sound (w := (78357 / 921643)) (n := 12)
    (lo := (170449113 / 1000000000)) (hi := (85224557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421643) = 1/(421643 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-85224557 / 500000000) (-170449113 / 1000000000) (Real.log (421643 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145851191 / 1000000000) ≤ -Real.log (31250 / 36157) ∧
    -Real.log (31250 / 36157) ≤ (18231399 / 125000000) := by
  have h := checkLog_sound (w := (4907 / 67407)) (n := 12)
    (lo := (145851191 / 1000000000)) (hi := (18231399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36157 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36157 / 31250) = 1/(31250 / 36157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145851191 / 1000000000) (18231399 / 125000000) (Real.log (36157 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (36157 / 31250) = -Real.log (31250 / 36157) := by
    rw [show ((36157 / 31250) : ℝ) = ((31250 / 36157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170816791 / 1000000000) ≤ -Real.log (26343 / 31250) ∧
    -Real.log (26343 / 31250) ≤ (21352099 / 125000000) := by
  have h := checkLog_sound (w := (4907 / 57593)) (n := 12)
    (lo := (170816791 / 1000000000)) (hi := (21352099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26343) = 1/(26343 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21352099 / 125000000) (-170816791 / 1000000000) (Real.log (26343 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (636685839 / 1000000000) ≤ -Real.log (500000000000 / 945103020039) ∧
    -Real.log (500000000000 / 945103020039) ≤ (7958573 / 12500000) := by
  have h := checkLog_sound (w := (445103020039 / 1445103020039)) (n := 12)
    (lo := (636685839 / 1000000000)) (hi := (7958573 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945103020039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945103020039 / 500000000000) = 1/(500000000000 / 945103020039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (636685839 / 1000000000) (7958573 / 12500000) (Real.log (945103020039 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (945103020039 / 500000000000) = -Real.log (500000000000 / 945103020039) := by
    rw [show ((945103020039 / 500000000000) : ℝ) = ((500000000000 / 945103020039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (637980799 / 1000000000) ≤ -Real.log (15625000000 / 29572740113) ∧
    -Real.log (15625000000 / 29572740113) ≤ (199369 / 312500) := by
  have h := checkLog_sound (w := (13947740113 / 45197740113)) (n := 12)
    (lo := (637980799 / 1000000000)) (hi := (199369 / 312500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29572740113 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29572740113 / 15625000000) = 1/(15625000000 / 29572740113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (637980799 / 1000000000) (199369 / 312500) (Real.log (29572740113 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (29572740113 / 15625000000) = -Real.log (15625000000 / 29572740113) := by
    rw [show ((29572740113 / 15625000000) : ℝ) = ((15625000000 / 29572740113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (27784987 / 62500000) ≤ -Real.log (500000000000 / 779901703549) ∧
    -Real.log (500000000000 / 779901703549) ≤ (444559793 / 1000000000) := by
  have h := checkLog_sound (w := (279901703549 / 1279901703549)) (n := 12)
    (lo := (27784987 / 62500000)) (hi := (444559793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779901703549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779901703549 / 500000000000) = 1/(500000000000 / 779901703549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27784987 / 62500000) (444559793 / 1000000000) (Real.log (779901703549 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (779901703549 / 500000000000) = -Real.log (500000000000 / 779901703549) := by
    rw [show ((779901703549 / 500000000000) : ℝ) = ((500000000000 / 779901703549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (445444169 / 1000000000) ≤ -Real.log (50000000000 / 78059173583) ∧
    -Real.log (50000000000 / 78059173583) ≤ (44544417 / 100000000) := by
  have h := checkLog_sound (w := (28059173583 / 128059173583)) (n := 12)
    (lo := (445444169 / 1000000000)) (hi := (44544417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78059173583 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78059173583 / 50000000000) = 1/(50000000000 / 78059173583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (445444169 / 1000000000) (44544417 / 100000000) (Real.log (78059173583 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (78059173583 / 50000000000) = -Real.log (50000000000 / 78059173583) := by
    rw [show ((78059173583 / 50000000000) : ℝ) = ((50000000000 / 78059173583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (15801617 / 50000000) ≤ -Real.log (62500000000 / 85729663483) ∧
    -Real.log (62500000000 / 85729663483) ≤ (316032341 / 1000000000) := by
  have h := checkLog_sound (w := (23229663483 / 148229663483)) (n := 12)
    (lo := (15801617 / 50000000)) (hi := (316032341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85729663483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85729663483 / 62500000000) = 1/(62500000000 / 85729663483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (15801617 / 50000000) (316032341 / 1000000000) (Real.log (85729663483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (85729663483 / 62500000000) = -Real.log (62500000000 / 85729663483) := by
    rw [show ((85729663483 / 62500000000) : ℝ) = ((62500000000 / 85729663483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (158333991 / 500000000) ≤ -Real.log (15625000000 / 21446043541) ∧
    -Real.log (15625000000 / 21446043541) ≤ (316667983 / 1000000000) := by
  have h := checkLog_sound (w := (5821043541 / 37071043541)) (n := 12)
    (lo := (158333991 / 500000000)) (hi := (316667983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21446043541 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21446043541 / 15625000000) = 1/(15625000000 / 21446043541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (158333991 / 500000000) (316667983 / 1000000000) (Real.log (21446043541 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21446043541 / 15625000000) = -Real.log (15625000000 / 21446043541) := by
    rw [show ((21446043541 / 15625000000) : ℝ) = ((15625000000 / 21446043541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24965599 / 1000000000) ≤ -Real.log (952483851 / 976562500) ∧
    -Real.log (952483851 / 976562500) ≤ (31207 / 1250000) := by
  have h := checkLog_sound (w := (24078649 / 1929046351)) (n := 12)
    (lo := (24965599 / 1000000000)) (hi := (31207 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 952483851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 952483851) = 1/(952483851 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31207 / 1250000) (-24965599 / 1000000000) (Real.log (952483851 / 976562500)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24865887 / 1000000000) ≤ -Real.log (243860180551 / 250000000000) ∧
    -Real.log (243860180551 / 250000000000) ≤ (777059 / 31250000) := by
  have h := checkLog_sound (w := (6139819449 / 493860180551)) (n := 12)
    (lo := (24865887 / 1000000000)) (hi := (777059 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243860180551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243860180551) = 1/(243860180551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-777059 / 31250000) (-24865887 / 1000000000) (Real.log (243860180551 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell099

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell100Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell100
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

theorem reflection_log_1_neg : (67350187 / 250000000) ≤ -Real.log (5120 / 6703) ∧
    -Real.log (5120 / 6703) ≤ (269400749 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 11823)) (n := 12)
    (lo := (67350187 / 250000000)) (hi := (269400749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6703 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6703 / 5120) = 1/(5120 / 6703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67350187 / 250000000) (269400749 / 1000000000) (Real.log (6703 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6703 / 5120) = -Real.log (5120 / 6703) := by
    rw [show ((6703 / 5120) : ℝ) = ((5120 / 6703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (46234441 / 125000000) ≤ -Real.log (3537 / 5120) ∧
    -Real.log (3537 / 5120) ≤ (369875529 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 8657)) (n := 12)
    (lo := (46234441 / 125000000)) (hi := (369875529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3537) = 1/(3537 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-369875529 / 1000000000) (-46234441 / 125000000) (Real.log (3537 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (268953087 / 1000000000) ≤ -Real.log (256 / 335) ∧
    -Real.log (256 / 335) ≤ (525299 / 1953125) := by
  have h := checkLog_sound (w := (79 / 591)) (n := 12)
    (lo := (268953087 / 1000000000)) (hi := (525299 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335 / 256) = 1/(256 / 335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (268953087 / 1000000000) (525299 / 1953125) (Real.log (335 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (335 / 256) = -Real.log (256 / 335) := by
    rw [show ((335 / 256) : ℝ) = ((256 / 335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (369027711 / 1000000000) ≤ -Real.log (177 / 256) ∧
    -Real.log (177 / 256) ≤ (2883029 / 7812500) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 177) = 1/(177 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2883029 / 7812500) (-369027711 / 1000000000) (Real.log (177 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (198119443 / 1000000000) ≤ -Real.log (250000 / 304777) ∧
    -Real.log (250000 / 304777) ≤ (49529861 / 250000000) := by
  have h := checkLog_sound (w := (54777 / 554777)) (n := 12)
    (lo := (198119443 / 1000000000)) (hi := (49529861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304777 / 250000) = 1/(250000 / 304777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (198119443 / 1000000000) (49529861 / 250000000) (Real.log (304777 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (304777 / 250000) = -Real.log (250000 / 304777) := by
    rw [show ((304777 / 250000) : ℝ) = ((250000 / 304777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (123659211 / 500000000) ≤ -Real.log (195223 / 250000) ∧
    -Real.log (195223 / 250000) ≤ (247318423 / 1000000000) := by
  have h := checkLog_sound (w := (54777 / 445223)) (n := 12)
    (lo := (123659211 / 500000000)) (hi := (247318423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195223) = 1/(195223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247318423 / 1000000000) (-123659211 / 500000000) (Real.log (195223 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99233999 / 500000000) ≤ -Real.log (1000000 / 1219533) ∧
    -Real.log (1000000 / 1219533) ≤ (198467999 / 1000000000) := by
  have h := checkLog_sound (w := (219533 / 2219533)) (n := 12)
    (lo := (99233999 / 500000000)) (hi := (198467999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219533 / 1000000) = 1/(1000000 / 1219533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99233999 / 500000000) (198467999 / 1000000000) (Real.log (1219533 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1219533 / 1000000) = -Real.log (1000000 / 1219533) := by
    rw [show ((1219533 / 1000000) : ℝ) = ((1000000 / 1219533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12393141 / 50000000) ≤ -Real.log (780467 / 1000000) ∧
    -Real.log (780467 / 1000000) ≤ (247862821 / 1000000000) := by
  have h := checkLog_sound (w := (219533 / 1780467)) (n := 12)
    (lo := (12393141 / 50000000)) (hi := (247862821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780467) = 1/(780467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-247862821 / 1000000000) (-12393141 / 50000000) (Real.log (780467 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145850327 / 1000000000) ≤ -Real.log (1000000 / 1157023) ∧
    -Real.log (1000000 / 1157023) ≤ (18231291 / 125000000) := by
  have h := checkLog_sound (w := (157023 / 2157023)) (n := 12)
    (lo := (145850327 / 1000000000)) (hi := (18231291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157023 / 1000000) = 1/(1000000 / 1157023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145850327 / 1000000000) (18231291 / 125000000) (Real.log (1157023 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1157023 / 1000000) = -Real.log (1000000 / 1157023) := by
    rw [show ((1157023 / 1000000) : ℝ) = ((1000000 / 1157023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42703901 / 250000000) ≤ -Real.log (842977 / 1000000) ∧
    -Real.log (842977 / 1000000) ≤ (34163121 / 200000000) := by
  have h := checkLog_sound (w := (157023 / 1842977)) (n := 12)
    (lo := (42703901 / 250000000)) (hi := (34163121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842977) = 1/(842977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34163121 / 200000000) (-42703901 / 250000000) (Real.log (842977 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7305911 / 50000000) ≤ -Real.log (1000000 / 1157333) ∧
    -Real.log (1000000 / 1157333) ≤ (146118221 / 1000000000) := by
  have h := checkLog_sound (w := (157333 / 2157333)) (n := 12)
    (lo := (7305911 / 50000000)) (hi := (146118221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157333 / 1000000) = 1/(1000000 / 1157333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7305911 / 50000000) (146118221 / 1000000000) (Real.log (1157333 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1157333 / 1000000) = -Real.log (1000000 / 1157333) := by
    rw [show ((1157333 / 1000000) : ℝ) = ((1000000 / 1157333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21397927 / 125000000) ≤ -Real.log (842667 / 1000000) ∧
    -Real.log (842667 / 1000000) ≤ (171183417 / 1000000000) := by
  have h := checkLog_sound (w := (157333 / 1842667)) (n := 12)
    (lo := (21397927 / 125000000)) (hi := (171183417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842667) = 1/(842667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171183417 / 1000000000) (-21397927 / 125000000) (Real.log (842667 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (637980799 / 1000000000) ≤ -Real.log (100000000000 / 189265536723) ∧
    -Real.log (100000000000 / 189265536723) ≤ (199369 / 312500) := by
  have h := checkLog_sound (w := (89265536723 / 289265536723)) (n := 12)
    (lo := (637980799 / 1000000000)) (hi := (199369 / 312500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189265536723 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189265536723 / 100000000000) = 1/(100000000000 / 189265536723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (637980799 / 1000000000) (199369 / 312500) (Real.log (189265536723 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (189265536723 / 100000000000) = -Real.log (100000000000 / 189265536723) := by
    rw [show ((189265536723 / 100000000000) : ℝ) = ((100000000000 / 189265536723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (639276277 / 1000000000) ≤ -Real.log (250000000000 / 473777212327) ∧
    -Real.log (250000000000 / 473777212327) ≤ (319638139 / 500000000) := by
  have h := checkLog_sound (w := (223777212327 / 723777212327)) (n := 12)
    (lo := (639276277 / 1000000000)) (hi := (319638139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473777212327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473777212327 / 250000000000) = 1/(250000000000 / 473777212327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (639276277 / 1000000000) (319638139 / 500000000) (Real.log (473777212327 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (473777212327 / 250000000000) = -Real.log (250000000000 / 473777212327) := by
    rw [show ((473777212327 / 250000000000) : ℝ) = ((250000000000 / 473777212327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (222718933 / 500000000) ≤ -Real.log (250000000000 / 390293408051) ∧
    -Real.log (250000000000 / 390293408051) ≤ (445437867 / 1000000000) := by
  have h := checkLog_sound (w := (140293408051 / 640293408051)) (n := 12)
    (lo := (222718933 / 500000000)) (hi := (445437867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390293408051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390293408051 / 250000000000) = 1/(250000000000 / 390293408051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222718933 / 500000000) (445437867 / 1000000000) (Real.log (390293408051 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390293408051 / 250000000000) = -Real.log (250000000000 / 390293408051) := by
    rw [show ((390293408051 / 250000000000) : ℝ) = ((250000000000 / 390293408051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (446330819 / 1000000000) ≤ -Real.log (500000000000 / 781284154231) ∧
    -Real.log (500000000000 / 781284154231) ≤ (22316541 / 50000000) := by
  have h := checkLog_sound (w := (281284154231 / 1281284154231)) (n := 12)
    (lo := (446330819 / 1000000000)) (hi := (22316541 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781284154231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781284154231 / 500000000000) = 1/(500000000000 / 781284154231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (446330819 / 1000000000) (22316541 / 50000000) (Real.log (781284154231 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (781284154231 / 500000000000) = -Real.log (500000000000 / 781284154231) := by
    rw [show ((781284154231 / 500000000000) : ℝ) = ((500000000000 / 781284154231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (316665931 / 1000000000) ≤ -Real.log (125000000000 / 171567996517) ∧
    -Real.log (125000000000 / 171567996517) ≤ (79166483 / 250000000) := by
  have h := checkLog_sound (w := (46567996517 / 296567996517)) (n := 12)
    (lo := (316665931 / 1000000000)) (hi := (79166483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171567996517 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171567996517 / 125000000000) = 1/(125000000000 / 171567996517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (316665931 / 1000000000) (79166483 / 250000000) (Real.log (171567996517 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171567996517 / 125000000000) = -Real.log (125000000000 / 171567996517) := by
    rw [show ((171567996517 / 125000000000) : ℝ) = ((125000000000 / 171567996517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79325409 / 250000000) ≤ -Real.log (250000000000 / 343354195667) ∧
    -Real.log (250000000000 / 343354195667) ≤ (317301637 / 1000000000) := by
  have h := checkLog_sound (w := (93354195667 / 593354195667)) (n := 12)
    (lo := (79325409 / 250000000)) (hi := (317301637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343354195667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343354195667 / 250000000000) = 1/(250000000000 / 343354195667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79325409 / 250000000) (317301637 / 1000000000) (Real.log (343354195667 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (343354195667 / 250000000000) = -Real.log (250000000000 / 343354195667) := by
    rw [show ((343354195667 / 250000000000) : ℝ) = ((250000000000 / 343354195667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6266299 / 250000000) ≤ -Real.log (975246327111 / 1000000000000) ∧
    -Real.log (975246327111 / 1000000000000) ≤ (25065197 / 1000000000) := by
  have h := checkLog_sound (w := (24753672889 / 1975246327111)) (n := 12)
    (lo := (6266299 / 250000000)) (hi := (25065197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975246327111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975246327111) = 1/(975246327111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25065197 / 1000000000) (-6266299 / 250000000) (Real.log (975246327111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24965277 / 1000000000) ≤ -Real.log (975343777471 / 1000000000000) ∧
    -Real.log (975343777471 / 1000000000000) ≤ (12482639 / 500000000) := by
  have h := checkLog_sound (w := (24656222529 / 1975343777471)) (n := 12)
    (lo := (24965277 / 1000000000)) (hi := (12482639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975343777471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975343777471) = 1/(975343777471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-12482639 / 500000000) (-24965277 / 1000000000) (Real.log (975343777471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell100

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell101Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell101
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

theorem reflection_log_1_neg : (16865513 / 62500000) ≤ -Real.log (2560 / 3353) ∧
    -Real.log (2560 / 3353) ≤ (269848209 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 5913)) (n := 12)
    (lo := (16865513 / 62500000)) (hi := (269848209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3353 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3353 / 2560) = 1/(2560 / 3353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16865513 / 62500000) (269848209 / 1000000000) (Real.log (3353 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3353 / 2560) = -Real.log (2560 / 3353) := by
    rw [show ((3353 / 2560) : ℝ) = ((2560 / 3353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74144813 / 200000000) ≤ -Real.log (1767 / 2560) ∧
    -Real.log (1767 / 2560) ≤ (185362033 / 500000000) := by
  have h := checkLog_sound (w := (793 / 4327)) (n := 12)
    (lo := (74144813 / 200000000)) (hi := (185362033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1767) = 1/(1767 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-185362033 / 500000000) (-74144813 / 200000000) (Real.log (1767 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67350187 / 250000000) ≤ -Real.log (5120 / 6703) ∧
    -Real.log (5120 / 6703) ≤ (269400749 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 11823)) (n := 12)
    (lo := (67350187 / 250000000)) (hi := (269400749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6703 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6703 / 5120) = 1/(5120 / 6703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67350187 / 250000000) (269400749 / 1000000000) (Real.log (6703 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6703 / 5120) = -Real.log (5120 / 6703) := by
    rw [show ((6703 / 5120) : ℝ) = ((5120 / 6703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (46234441 / 125000000) ≤ -Real.log (3537 / 5120) ∧
    -Real.log (3537 / 5120) ≤ (369875529 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 8657)) (n := 12)
    (lo := (46234441 / 125000000)) (hi := (369875529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3537) = 1/(3537 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-369875529 / 1000000000) (-46234441 / 125000000) (Real.log (3537 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99232769 / 500000000) ≤ -Real.log (100000 / 121953) ∧
    -Real.log (100000 / 121953) ≤ (198465539 / 1000000000) := by
  have h := checkLog_sound (w := (21953 / 221953)) (n := 12)
    (lo := (99232769 / 500000000)) (hi := (198465539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121953 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121953 / 100000) = 1/(100000 / 121953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99232769 / 500000000) (198465539 / 1000000000) (Real.log (121953 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121953 / 100000) = -Real.log (100000 / 121953) := by
    rw [show ((121953 / 100000) : ℝ) = ((100000 / 121953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7745593 / 31250000) ≤ -Real.log (78047 / 100000) ∧
    -Real.log (78047 / 100000) ≤ (247858977 / 1000000000) := by
  have h := checkLog_sound (w := (21953 / 178047)) (n := 12)
    (lo := (7745593 / 31250000)) (hi := (247858977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78047) = 1/(78047 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247858977 / 1000000000) (-7745593 / 31250000) (Real.log (78047 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99404937 / 500000000) ≤ -Real.log (20000 / 24399) ∧
    -Real.log (20000 / 24399) ≤ (1590479 / 8000000) := by
  have h := checkLog_sound (w := (4399 / 44399)) (n := 12)
    (lo := (99404937 / 500000000)) (hi := (1590479 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24399 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24399 / 20000) = 1/(20000 / 24399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99404937 / 500000000) (1590479 / 8000000) (Real.log (24399 / 20000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24399 / 20000) = -Real.log (20000 / 24399) := by
    rw [show ((24399 / 20000) : ℝ) = ((20000 / 24399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (124198629 / 500000000) ≤ -Real.log (15601 / 20000) ∧
    -Real.log (15601 / 20000) ≤ (248397259 / 1000000000) := by
  have h := checkLog_sound (w := (4399 / 35601)) (n := 12)
    (lo := (124198629 / 500000000)) (hi := (248397259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15601) = 1/(15601 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248397259 / 1000000000) (-124198629 / 500000000) (Real.log (15601 / 20000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36529339 / 250000000) ≤ -Real.log (250000 / 289333) ∧
    -Real.log (250000 / 289333) ≤ (146117357 / 1000000000) := by
  have h := checkLog_sound (w := (39333 / 539333)) (n := 12)
    (lo := (36529339 / 250000000)) (hi := (146117357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289333 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289333 / 250000) = 1/(250000 / 289333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36529339 / 250000000) (146117357 / 1000000000) (Real.log (289333 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (289333 / 250000) = -Real.log (250000 / 289333) := by
    rw [show ((289333 / 250000) : ℝ) = ((250000 / 289333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17118223 / 100000000) ≤ -Real.log (210667 / 250000) ∧
    -Real.log (210667 / 250000) ≤ (171182231 / 1000000000) := by
  have h := checkLog_sound (w := (39333 / 460667)) (n := 12)
    (lo := (17118223 / 100000000)) (hi := (171182231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 210667) = 1/(210667 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171182231 / 1000000000) (-17118223 / 100000000) (Real.log (210667 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146385177 / 1000000000) ≤ -Real.log (500000 / 578821) ∧
    -Real.log (500000 / 578821) ≤ (73192589 / 500000000) := by
  have h := checkLog_sound (w := (78821 / 1078821)) (n := 12)
    (lo := (146385177 / 1000000000)) (hi := (73192589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578821 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578821 / 500000) = 1/(500000 / 578821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146385177 / 1000000000) (73192589 / 500000000) (Real.log (578821 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (578821 / 500000) = -Real.log (500000 / 578821) := by
    rw [show ((578821 / 500000) : ℝ) = ((500000 / 578821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5360943 / 31250000) ≤ -Real.log (421179 / 500000) ∧
    -Real.log (421179 / 500000) ≤ (171550177 / 1000000000) := by
  have h := checkLog_sound (w := (78821 / 921179)) (n := 12)
    (lo := (5360943 / 31250000)) (hi := (171550177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421179) = 1/(421179 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171550177 / 1000000000) (-5360943 / 31250000) (Real.log (421179 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (639276277 / 1000000000) ≤ -Real.log (500000000000 / 947554424653) ∧
    -Real.log (500000000000 / 947554424653) ≤ (319638139 / 500000000) := by
  have h := checkLog_sound (w := (447554424653 / 1447554424653)) (n := 12)
    (lo := (639276277 / 1000000000)) (hi := (319638139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((947554424653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(947554424653 / 500000000000) = 1/(500000000000 / 947554424653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (639276277 / 1000000000) (319638139 / 500000000) (Real.log (947554424653 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (947554424653 / 500000000000) = -Real.log (500000000000 / 947554424653) := by
    rw [show ((947554424653 / 500000000000) : ℝ) = ((500000000000 / 947554424653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (320286137 / 500000000) ≤ -Real.log (125000000000 / 237195812111) ∧
    -Real.log (125000000000 / 237195812111) ≤ (25622891 / 40000000) := by
  have h := checkLog_sound (w := (112195812111 / 362195812111)) (n := 12)
    (lo := (320286137 / 500000000)) (hi := (25622891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237195812111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237195812111 / 125000000000) = 1/(125000000000 / 237195812111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (320286137 / 500000000) (25622891 / 40000000) (Real.log (237195812111 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (237195812111 / 125000000000) = -Real.log (125000000000 / 237195812111) := by
    rw [show ((237195812111 / 125000000000) : ℝ) = ((125000000000 / 237195812111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (89264903 / 200000000) ≤ -Real.log (250000000000 / 390639614591) ∧
    -Real.log (250000000000 / 390639614591) ≤ (111581129 / 250000000) := by
  have h := checkLog_sound (w := (140639614591 / 640639614591)) (n := 12)
    (lo := (89264903 / 200000000)) (hi := (111581129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390639614591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390639614591 / 250000000000) = 1/(250000000000 / 390639614591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (89264903 / 200000000) (111581129 / 250000000) (Real.log (390639614591 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390639614591 / 250000000000) = -Real.log (250000000000 / 390639614591) := by
    rw [show ((390639614591 / 250000000000) : ℝ) = ((250000000000 / 390639614591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (447207133 / 1000000000) ≤ -Real.log (100000000000 / 156393820909) ∧
    -Real.log (100000000000 / 156393820909) ≤ (223603567 / 500000000) := by
  have h := checkLog_sound (w := (56393820909 / 256393820909)) (n := 12)
    (lo := (447207133 / 1000000000)) (hi := (223603567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156393820909 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156393820909 / 100000000000) = 1/(100000000000 / 156393820909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (447207133 / 1000000000) (223603567 / 500000000) (Real.log (156393820909 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (156393820909 / 100000000000) = -Real.log (100000000000 / 156393820909) := by
    rw [show ((156393820909 / 100000000000) : ℝ) = ((100000000000 / 156393820909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (158649793 / 500000000) ≤ -Real.log (250000000000 / 343353491529) ∧
    -Real.log (250000000000 / 343353491529) ≤ (317299587 / 1000000000) := by
  have h := checkLog_sound (w := (93353491529 / 593353491529)) (n := 12)
    (lo := (158649793 / 500000000)) (hi := (317299587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343353491529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343353491529 / 250000000000) = 1/(250000000000 / 343353491529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (158649793 / 500000000) (317299587 / 1000000000) (Real.log (343353491529 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (343353491529 / 250000000000) = -Real.log (250000000000 / 343353491529) := by
    rw [show ((343353491529 / 250000000000) : ℝ) = ((250000000000 / 343353491529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (158967677 / 500000000) ≤ -Real.log (100000000000 / 137428741699) ∧
    -Real.log (100000000000 / 137428741699) ≤ (63587071 / 200000000) := by
  have h := checkLog_sound (w := (37428741699 / 237428741699)) (n := 12)
    (lo := (158967677 / 500000000)) (hi := (63587071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137428741699 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137428741699 / 100000000000) = 1/(100000000000 / 137428741699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (158967677 / 500000000) (63587071 / 200000000) (Real.log (137428741699 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137428741699 / 100000000000) = -Real.log (100000000000 / 137428741699) := by
    rw [show ((137428741699 / 100000000000) : ℝ) = ((100000000000 / 137428741699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25164999 / 1000000000) ≤ -Real.log (243787249959 / 250000000000) ∧
    -Real.log (243787249959 / 250000000000) ≤ (5033 / 200000) := by
  have h := checkLog_sound (w := (6212750041 / 493787249959)) (n := 12)
    (lo := (25164999 / 1000000000)) (hi := (5033 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243787249959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243787249959) = 1/(243787249959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5033 / 200000) (-25164999 / 1000000000) (Real.log (243787249959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12532437 / 500000000) ≤ -Real.log (60952915111 / 62500000000) ∧
    -Real.log (60952915111 / 62500000000) ≤ (200519 / 8000000) := by
  have h := checkLog_sound (w := (1547084889 / 123452915111)) (n := 12)
    (lo := (12532437 / 500000000)) (hi := (200519 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60952915111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60952915111) = 1/(60952915111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-200519 / 8000000) (-12532437 / 500000000) (Real.log (60952915111 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell101

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell102Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell102
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

theorem reflection_log_1_neg : (270295469 / 1000000000) ≤ -Real.log (5120 / 6709) ∧
    -Real.log (5120 / 6709) ≤ (27029547 / 100000000) := by
  have h := checkLog_sound (w := (1589 / 11829)) (n := 12)
    (lo := (270295469 / 1000000000)) (hi := (27029547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6709 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6709 / 5120) = 1/(5120 / 6709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (270295469 / 1000000000) (27029547 / 100000000) (Real.log (6709 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6709 / 5120) = -Real.log (5120 / 6709) := by
    rw [show ((6709 / 5120) : ℝ) = ((5120 / 6709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (185786661 / 500000000) ≤ -Real.log (3531 / 5120) ∧
    -Real.log (3531 / 5120) ≤ (371573323 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 8651)) (n := 12)
    (lo := (185786661 / 500000000)) (hi := (371573323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3531) = 1/(3531 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-371573323 / 1000000000) (-185786661 / 500000000) (Real.log (3531 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16865513 / 62500000) ≤ -Real.log (2560 / 3353) ∧
    -Real.log (2560 / 3353) ≤ (269848209 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 5913)) (n := 12)
    (lo := (16865513 / 62500000)) (hi := (269848209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3353 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3353 / 2560) = 1/(2560 / 3353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16865513 / 62500000) (269848209 / 1000000000) (Real.log (3353 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3353 / 2560) = -Real.log (2560 / 3353) := by
    rw [show ((3353 / 2560) : ℝ) = ((2560 / 3353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74144813 / 200000000) ≤ -Real.log (1767 / 2560) ∧
    -Real.log (1767 / 2560) ≤ (185362033 / 500000000) := by
  have h := checkLog_sound (w := (793 / 4327)) (n := 12)
    (lo := (74144813 / 200000000)) (hi := (185362033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1767) = 1/(1767 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-185362033 / 500000000) (-74144813 / 200000000) (Real.log (1767 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99404527 / 500000000) ≤ -Real.log (1000000 / 1219949) ∧
    -Real.log (1000000 / 1219949) ≤ (39761811 / 200000000) := by
  have h := checkLog_sound (w := (219949 / 2219949)) (n := 12)
    (lo := (99404527 / 500000000)) (hi := (39761811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219949 / 1000000) = 1/(1000000 / 1219949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99404527 / 500000000) (39761811 / 200000000) (Real.log (1219949 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1219949 / 1000000) = -Real.log (1000000 / 1219949) := by
    rw [show ((1219949 / 1000000) : ℝ) = ((1000000 / 1219949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31049497 / 125000000) ≤ -Real.log (780051 / 1000000) ∧
    -Real.log (780051 / 1000000) ≤ (248395977 / 1000000000) := by
  have h := checkLog_sound (w := (219949 / 1780051)) (n := 12)
    (lo := (31049497 / 125000000)) (hi := (248395977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780051) = 1/(780051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248395977 / 1000000000) (-31049497 / 125000000) (Real.log (780051 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199154091 / 1000000000) ≤ -Real.log (100000 / 122037) ∧
    -Real.log (100000 / 122037) ≤ (49788523 / 250000000) := by
  have h := checkLog_sound (w := (22037 / 222037)) (n := 12)
    (lo := (199154091 / 1000000000)) (hi := (49788523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122037 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122037 / 100000) = 1/(100000 / 122037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199154091 / 1000000000) (49788523 / 250000000) (Real.log (122037 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (122037 / 100000) = -Real.log (100000 / 122037) := by
    rw [show ((122037 / 100000) : ℝ) = ((100000 / 122037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (24893583 / 100000000) ≤ -Real.log (77963 / 100000) ∧
    -Real.log (77963 / 100000) ≤ (248935831 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 177963)) (n := 12)
    (lo := (24893583 / 100000000)) (hi := (248935831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77963) = 1/(77963 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248935831 / 1000000000) (-24893583 / 100000000) (Real.log (77963 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (146384313 / 1000000000) ≤ -Real.log (1000000 / 1157641) ∧
    -Real.log (1000000 / 1157641) ≤ (73192157 / 500000000) := by
  have h := checkLog_sound (w := (157641 / 2157641)) (n := 12)
    (lo := (146384313 / 1000000000)) (hi := (73192157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157641 / 1000000) = 1/(1000000 / 1157641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (146384313 / 1000000000) (73192157 / 500000000) (Real.log (1157641 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1157641 / 1000000) = -Real.log (1000000 / 1157641) := by
    rw [show ((1157641 / 1000000) : ℝ) = ((1000000 / 1157641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (171548989 / 1000000000) ≤ -Real.log (842359 / 1000000) ∧
    -Real.log (842359 / 1000000) ≤ (17154899 / 100000000) := by
  have h := checkLog_sound (w := (157641 / 1842359)) (n := 12)
    (lo := (171548989 / 1000000000)) (hi := (17154899 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842359) = 1/(842359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17154899 / 100000000) (-171548989 / 1000000000) (Real.log (842359 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146652063 / 1000000000) ≤ -Real.log (1000000 / 1157951) ∧
    -Real.log (1000000 / 1157951) ≤ (4582877 / 31250000) := by
  have h := checkLog_sound (w := (157951 / 2157951)) (n := 12)
    (lo := (146652063 / 1000000000)) (hi := (4582877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157951 / 1000000) = 1/(1000000 / 1157951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146652063 / 1000000000) (4582877 / 31250000) (Real.log (1157951 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1157951 / 1000000) = -Real.log (1000000 / 1157951) := by
    rw [show ((1157951 / 1000000) : ℝ) = ((1000000 / 1157951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (171917071 / 1000000000) ≤ -Real.log (842049 / 1000000) ∧
    -Real.log (842049 / 1000000) ≤ (10744817 / 62500000) := by
  have h := checkLog_sound (w := (157951 / 1842049)) (n := 12)
    (lo := (171917071 / 1000000000)) (hi := (10744817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842049) = 1/(842049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10744817 / 62500000) (-171917071 / 1000000000) (Real.log (842049 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (320286137 / 500000000) ≤ -Real.log (500000000000 / 948783248443) ∧
    -Real.log (500000000000 / 948783248443) ≤ (25622891 / 40000000) := by
  have h := checkLog_sound (w := (448783248443 / 1448783248443)) (n := 12)
    (lo := (320286137 / 500000000)) (hi := (25622891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948783248443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948783248443 / 500000000000) = 1/(500000000000 / 948783248443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (320286137 / 500000000) (25622891 / 40000000) (Real.log (948783248443 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (948783248443 / 500000000000) = -Real.log (500000000000 / 948783248443) := by
    rw [show ((948783248443 / 500000000000) : ℝ) = ((500000000000 / 948783248443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (641868791 / 1000000000) ≤ -Real.log (100000000000 / 190002832059) ∧
    -Real.log (100000000000 / 190002832059) ≤ (80233599 / 125000000) := by
  have h := checkLog_sound (w := (90002832059 / 290002832059)) (n := 12)
    (lo := (641868791 / 1000000000)) (hi := (80233599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190002832059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190002832059 / 100000000000) = 1/(100000000000 / 190002832059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (641868791 / 1000000000) (80233599 / 125000000) (Real.log (190002832059 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (190002832059 / 100000000000) = -Real.log (100000000000 / 190002832059) := by
    rw [show ((190002832059 / 100000000000) : ℝ) = ((100000000000 / 190002832059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (447205031 / 1000000000) ≤ -Real.log (500000000000 / 781967461101) ∧
    -Real.log (500000000000 / 781967461101) ≤ (55900629 / 125000000) := by
  have h := checkLog_sound (w := (281967461101 / 1281967461101)) (n := 12)
    (lo := (447205031 / 1000000000)) (hi := (55900629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781967461101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781967461101 / 500000000000) = 1/(500000000000 / 781967461101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (447205031 / 1000000000) (55900629 / 125000000) (Real.log (781967461101 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (781967461101 / 500000000000) = -Real.log (500000000000 / 781967461101) := by
    rw [show ((781967461101 / 500000000000) : ℝ) = ((500000000000 / 781967461101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (224044961 / 500000000) ≤ -Real.log (500000000000 / 782659723203) ∧
    -Real.log (500000000000 / 782659723203) ≤ (448089923 / 1000000000) := by
  have h := checkLog_sound (w := (282659723203 / 1282659723203)) (n := 12)
    (lo := (224044961 / 500000000)) (hi := (448089923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782659723203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782659723203 / 500000000000) = 1/(500000000000 / 782659723203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (224044961 / 500000000) (448089923 / 1000000000) (Real.log (782659723203 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (782659723203 / 500000000000) = -Real.log (500000000000 / 782659723203) := by
    rw [show ((782659723203 / 500000000000) : ℝ) = ((500000000000 / 782659723203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (317933303 / 1000000000) ≤ -Real.log (100000000000 / 137428459837) ∧
    -Real.log (100000000000 / 137428459837) ≤ (39741663 / 125000000) := by
  have h := checkLog_sound (w := (37428459837 / 237428459837)) (n := 12)
    (lo := (317933303 / 1000000000)) (hi := (39741663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137428459837 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137428459837 / 100000000000) = 1/(100000000000 / 137428459837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (317933303 / 1000000000) (39741663 / 125000000) (Real.log (137428459837 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (137428459837 / 100000000000) = -Real.log (100000000000 / 137428459837) := by
    rw [show ((137428459837 / 100000000000) : ℝ) = ((100000000000 / 137428459837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (63713827 / 200000000) ≤ -Real.log (100000000000 / 137515869029) ∧
    -Real.log (100000000000 / 137515869029) ≤ (19910571 / 62500000) := by
  have h := checkLog_sound (w := (37515869029 / 237515869029)) (n := 12)
    (lo := (63713827 / 200000000)) (hi := (19910571 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137515869029 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137515869029 / 100000000000) = 1/(100000000000 / 137515869029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (63713827 / 200000000) (19910571 / 62500000) (Real.log (137515869029 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137515869029 / 100000000000) = -Real.log (100000000000 / 137515869029) := by
    rw [show ((137515869029 / 100000000000) : ℝ) = ((100000000000 / 137515869029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25265007 / 1000000000) ≤ -Real.log (975051481599 / 1000000000000) ∧
    -Real.log (975051481599 / 1000000000000) ≤ (1579063 / 62500000) := by
  have h := checkLog_sound (w := (24948518401 / 1975051481599)) (n := 12)
    (lo := (25265007 / 1000000000)) (hi := (1579063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975051481599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975051481599) = 1/(975051481599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1579063 / 62500000) (-25265007 / 1000000000) (Real.log (975051481599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1006587 / 40000000) ≤ -Real.log (975149315119 / 1000000000000) ∧
    -Real.log (975149315119 / 1000000000000) ≤ (6291169 / 250000000) := by
  have h := checkLog_sound (w := (24850684881 / 1975149315119)) (n := 12)
    (lo := (1006587 / 40000000)) (hi := (6291169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975149315119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975149315119) = 1/(975149315119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6291169 / 250000000) (-1006587 / 40000000) (Real.log (975149315119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell102

end


