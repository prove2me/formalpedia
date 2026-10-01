-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0126Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0126Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:46:46.745987+00:00
-- url     : https://prove2.me/theorems/e4ce57ec-228a-4284-b5d3-860943c3cf53
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0132Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0132Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0132Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0126Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0127Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0128Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0129Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0130Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0131Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0132Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0126
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

theorem reflection_log_1_neg : (331897401 / 500000000) ≤ -Real.log (25600 / 49719) ∧
    -Real.log (25600 / 49719) ≤ (663794803 / 1000000000) := by
  have h := checkLog_sound (w := (24119 / 75319)) (n := 12)
    (lo := (331897401 / 500000000)) (hi := (663794803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49719 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49719 / 25600) = 1/(25600 / 49719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331897401 / 500000000) (663794803 / 1000000000) (Real.log (49719 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49719 / 25600) = -Real.log (25600 / 49719) := by
    rw [show ((49719 / 25600) : ℝ) = ((25600 / 49719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2849874813 / 1000000000) ≤ -Real.log (1481 / 25600) ∧
    -Real.log (1481 / 25600) ≤ (1424937409 / 500000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1481) = 1/(1481 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1424937409 / 500000000) (-2849874813 / 1000000000) (Real.log (1481 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (31677737 / 50000000) ≤ -Real.log (12800 / 24119) ∧
    -Real.log (12800 / 24119) ≤ (633554741 / 1000000000) := by
  have h := checkLog_sound (w := (11319 / 36919)) (n := 12)
    (lo := (31677737 / 50000000)) (hi := (633554741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24119 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24119 / 12800) = 1/(12800 / 24119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (31677737 / 50000000) (633554741 / 1000000000) (Real.log (24119 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24119 / 12800) = -Real.log (12800 / 24119) := by
    rw [show ((24119 / 12800) : ℝ) = ((12800 / 24119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2156727633 / 1000000000) ≤ -Real.log (1481 / 12800) ∧
    -Real.log (1481 / 12800) ≤ (2156727637 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1481) = 1/(1481 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2156727637 / 1000000000) (-2156727633 / 1000000000) (Real.log (1481 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669318007 / 1000000000) ≤ -Real.log (200000 / 390581) ∧
    -Real.log (200000 / 390581) ≤ (83664751 / 125000000) := by
  have h := checkLog_sound (w := (190581 / 590581)) (n := 12)
    (lo := (669318007 / 1000000000)) (hi := (83664751 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390581 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390581 / 200000) = 1/(200000 / 390581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669318007 / 1000000000) (83664751 / 125000000) (Real.log (390581 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (390581 / 200000) = -Real.log (200000 / 390581) := by
    rw [show ((390581 / 200000) : ℝ) = ((200000 / 390581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1527794219 / 500000000) ≤ -Real.log (9419 / 200000) ∧
    -Real.log (9419 / 200000) ≤ (3055588443 / 1000000000) := by
  have h := checkLog_sound (w := (3081 / 21919)) (n := 12)
    (lo := (141499859 / 500000000)) (hi := (282999719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9419) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 9419) = 1/(9419 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3055588443 / 1000000000) (-1527794219 / 500000000) (Real.log (9419 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669602159 / 1000000000) ≤ -Real.log (50000 / 97673) ∧
    -Real.log (50000 / 97673) ≤ (8370027 / 12500000) := by
  have h := checkLog_sound (w := (47673 / 147673)) (n := 12)
    (lo := (669602159 / 1000000000)) (hi := (8370027 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97673 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97673 / 50000) = 1/(50000 / 97673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669602159 / 1000000000) (8370027 / 12500000) (Real.log (97673 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (97673 / 50000) = -Real.log (50000 / 97673) := by
    rw [show ((97673 / 50000) : ℝ) = ((50000 / 97673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1533721559 / 500000000) ≤ -Real.log (2327 / 50000) ∧
    -Real.log (2327 / 50000) ≤ (3067443123 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 2726)) (n := 12)
    (lo := (147427199 / 500000000)) (hi := (294854399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2327) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2327) = 1/(2327 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3067443123 / 1000000000) (-1533721559 / 500000000) (Real.log (2327 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668965137 / 1000000000) ≤ -Real.log (125000 / 244027) ∧
    -Real.log (125000 / 244027) ≤ (334482569 / 500000000) := by
  have h := checkLog_sound (w := (119027 / 369027)) (n := 12)
    (lo := (668965137 / 1000000000)) (hi := (334482569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244027 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244027 / 125000) = 1/(125000 / 244027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668965137 / 1000000000) (334482569 / 500000000) (Real.log (244027 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (244027 / 125000) = -Real.log (125000 / 244027) := by
    rw [show ((244027 / 125000) : ℝ) = ((125000 / 244027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3041064421 / 1000000000) ≤ -Real.log (5973 / 125000) ∧
    -Real.log (5973 / 125000) ≤ (1520532213 / 500000000) := by
  have h := checkLog_sound (w := (3679 / 27571)) (n := 12)
    (lo := (268475701 / 1000000000)) (hi := (134237851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11946) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11946) = 1/(5973 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1520532213 / 500000000) (-3041064421 / 1000000000) (Real.log (5973 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (669259631 / 1000000000) ≤ -Real.log (1000000 / 1952791) ∧
    -Real.log (1000000 / 1952791) ≤ (41828727 / 62500000) := by
  have h := checkLog_sound (w := (952791 / 2952791)) (n := 12)
    (lo := (669259631 / 1000000000)) (hi := (41828727 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952791 / 1000000) = 1/(1000000 / 1952791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (669259631 / 1000000000) (41828727 / 62500000) (Real.log (1952791 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1952791 / 1000000) = -Real.log (1000000 / 1952791) := by
    rw [show ((1952791 / 1000000) : ℝ) = ((1000000 / 1952791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (763292681 / 250000000) ≤ -Real.log (47209 / 1000000) ∧
    -Real.log (47209 / 1000000) ≤ (3053170729 / 1000000000) := by
  have h := checkLog_sound (w := (15291 / 109709)) (n := 12)
    (lo := (70145501 / 250000000)) (hi := (56116401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47209) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47209) = 1/(47209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3053170729 / 1000000000) (-763292681 / 250000000) (Real.log (47209 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (744981289 / 200000000) ≤ -Real.log (100000000000 / 4146735322221) ∧
    -Real.log (100000000000 / 4146735322221) ≤ (3724906451 / 1000000000) := by
  have h := checkLog_sound (w := (946735322221 / 7346735322221)) (n := 12)
    (lo := (51834109 / 200000000)) (hi := (129585273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4146735322221 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4146735322221 / 3200000000000) = 1/(100000000000 / 4146735322221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (744981289 / 200000000) (3724906451 / 1000000000) (Real.log (4146735322221 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4146735322221 / 100000000000) = -Real.log (100000000000 / 4146735322221) := by
    rw [show ((4146735322221 / 100000000000) : ℝ) = ((100000000000 / 4146735322221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3737045277 / 1000000000) ≤ -Real.log (500000000000 / 20986892995273) ∧
    -Real.log (500000000000 / 20986892995273) ≤ (3737045283 / 1000000000) := by
  have h := checkLog_sound (w := (4986892995273 / 36986892995273)) (n := 12)
    (lo := (271309377 / 1000000000)) (hi := (135654689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20986892995273 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20986892995273 / 16000000000000) = 1/(500000000000 / 20986892995273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3737045277 / 1000000000) (3737045283 / 1000000000) (Real.log (20986892995273 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20986892995273 / 500000000000) = -Real.log (500000000000 / 20986892995273) := by
    rw [show ((20986892995273 / 500000000000) : ℝ) = ((500000000000 / 20986892995273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1855014779 / 500000000) ≤ -Real.log (62500000000 / 2553438389419) ∧
    -Real.log (62500000000 / 2553438389419) ≤ (927507391 / 250000000) := by
  have h := checkLog_sound (w := (553438389419 / 4553438389419)) (n := 12)
    (lo := (122146829 / 500000000)) (hi := (244293659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553438389419 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2553438389419 / 2000000000000) = 1/(62500000000 / 2553438389419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1855014779 / 500000000) (927507391 / 250000000) (Real.log (2553438389419 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2553438389419 / 62500000000) = -Real.log (62500000000 / 2553438389419) := by
    rw [show ((2553438389419 / 62500000000) : ℝ) = ((62500000000 / 2553438389419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (744486071 / 200000000) ≤ -Real.log (500000000000 / 20682401660701) ∧
    -Real.log (500000000000 / 20682401660701) ≤ (3722430361 / 1000000000) := by
  have h := checkLog_sound (w := (4682401660701 / 36682401660701)) (n := 12)
    (lo := (51338891 / 200000000)) (hi := (32086807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20682401660701 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20682401660701 / 16000000000000) = 1/(500000000000 / 20682401660701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (744486071 / 200000000) (3722430361 / 1000000000) (Real.log (20682401660701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20682401660701 / 500000000000) = -Real.log (500000000000 / 20682401660701) := by
    rw [show ((20682401660701 / 500000000000) : ℝ) = ((500000000000 / 20682401660701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0126

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0127
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

theorem reflection_log_1_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331515107 / 500000000) ≤ -Real.log (25600 / 49681) ∧
    -Real.log (25600 / 49681) ≤ (132606043 / 200000000) := by
  have h := checkLog_sound (w := (24081 / 75281)) (n := 12)
    (lo := (331515107 / 500000000)) (hi := (132606043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49681 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49681 / 25600) = 1/(25600 / 49681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331515107 / 500000000) (132606043 / 200000000) (Real.log (49681 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49681 / 25600) = -Real.log (25600 / 49681) := by
    rw [show ((49681 / 25600) : ℝ) = ((25600 / 49681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22596321 / 8000000) ≤ -Real.log (1519 / 25600) ∧
    -Real.log (1519 / 25600) ≤ (282454013 / 100000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1519) = 1/(1519 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-282454013 / 100000000) (-22596321 / 8000000) (Real.log (1519 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78997247 / 125000000) ≤ -Real.log (12800 / 24081) ∧
    -Real.log (12800 / 24081) ≤ (631977977 / 1000000000) := by
  have h := checkLog_sound (w := (11281 / 36881)) (n := 12)
    (lo := (78997247 / 125000000)) (hi := (631977977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24081 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24081 / 12800) = 1/(12800 / 24081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78997247 / 125000000) (631977977 / 1000000000) (Real.log (24081 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24081 / 12800) = -Real.log (12800 / 24081) := by
    rw [show ((24081 / 12800) : ℝ) = ((12800 / 24081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (426278589 / 200000000) ≤ -Real.log (1519 / 12800) ∧
    -Real.log (1519 / 12800) ≤ (2131392949 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1519) = 1/(1519 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2131392949 / 1000000000) (-426278589 / 200000000) (Real.log (1519 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669034799 / 1000000000) ≤ -Real.log (31250 / 61011) ∧
    -Real.log (31250 / 61011) ≤ (1672587 / 2500000) := by
  have h := checkLog_sound (w := (29761 / 92261)) (n := 12)
    (lo := (669034799 / 1000000000)) (hi := (1672587 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61011 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61011 / 31250) = 1/(31250 / 61011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669034799 / 1000000000) (1672587 / 2500000) (Real.log (61011 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61011 / 31250) = -Real.log (31250 / 61011) := by
    rw [show ((61011 / 31250) : ℝ) = ((31250 / 61011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152195731 / 50000000) ≤ -Real.log (1489 / 31250) ∧
    -Real.log (1489 / 31250) ≤ (24351317 / 8000000) := by
  have h := checkLog_sound (w := (3713 / 27537)) (n := 12)
    (lo := (2713259 / 10000000)) (hi := (271325901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11912) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11912) = 1/(1489 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24351317 / 8000000) (-152195731 / 50000000) (Real.log (1489 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669318519 / 1000000000) ≤ -Real.log (500000 / 976453) ∧
    -Real.log (500000 / 976453) ≤ (16732963 / 25000000) := by
  have h := checkLog_sound (w := (476453 / 1476453)) (n := 12)
    (lo := (669318519 / 1000000000)) (hi := (16732963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976453 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976453 / 500000) = 1/(500000 / 976453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669318519 / 1000000000) (16732963 / 25000000) (Real.log (976453 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (976453 / 500000) = -Real.log (500000 / 976453) := by
    rw [show ((976453 / 500000) : ℝ) = ((500000 / 976453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (381951209 / 125000000) ≤ -Real.log (23547 / 500000) ∧
    -Real.log (23547 / 500000) ≤ (3055609677 / 1000000000) := by
  have h := checkLog_sound (w := (7703 / 54797)) (n := 12)
    (lo := (35377619 / 125000000)) (hi := (283020953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23547) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 23547) = 1/(23547 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3055609677 / 1000000000) (-381951209 / 125000000) (Real.log (23547 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668671581 / 1000000000) ≤ -Real.log (1000000 / 1951643) ∧
    -Real.log (1000000 / 1951643) ≤ (334335791 / 500000000) := by
  have h := checkLog_sound (w := (951643 / 2951643)) (n := 12)
    (lo := (668671581 / 1000000000)) (hi := (334335791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951643 / 1000000) = 1/(1000000 / 1951643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668671581 / 1000000000) (334335791 / 500000000) (Real.log (1951643 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1951643 / 1000000) = -Real.log (1000000 / 1951643) := by
    rw [show ((1951643 / 1000000) : ℝ) = ((1000000 / 1951643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3029144287 / 1000000000) ≤ -Real.log (48357 / 1000000) ∧
    -Real.log (48357 / 1000000) ≤ (757286073 / 250000000) := by
  have h := checkLog_sound (w := (14143 / 110857)) (n := 12)
    (lo := (256555567 / 1000000000)) (hi := (16034723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48357) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48357) = 1/(48357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-757286073 / 250000000) (-3029144287 / 1000000000) (Real.log (48357 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (668965649 / 1000000000) ≤ -Real.log (1000000 / 1952217) ∧
    -Real.log (1000000 / 1952217) ≤ (13379313 / 20000000) := by
  have h := checkLog_sound (w := (952217 / 2952217)) (n := 12)
    (lo := (668965649 / 1000000000)) (hi := (13379313 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952217 / 1000000) = 1/(1000000 / 1952217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (668965649 / 1000000000) (13379313 / 20000000) (Real.log (1952217 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1952217 / 1000000) = -Real.log (1000000 / 1952217) := by
    rw [show ((1952217 / 1000000) : ℝ) = ((1000000 / 1952217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3041085349 / 1000000000) ≤ -Real.log (47783 / 1000000) ∧
    -Real.log (47783 / 1000000) ≤ (1520542677 / 500000000) := by
  have h := checkLog_sound (w := (14717 / 110283)) (n := 12)
    (lo := (268496629 / 1000000000)) (hi := (26849663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47783) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47783) = 1/(47783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1520542677 / 500000000) (-3041085349 / 1000000000) (Real.log (47783 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3712949419 / 1000000000) ≤ -Real.log (250000000000 / 10243619879113) ∧
    -Real.log (250000000000 / 10243619879113) ≤ (148517977 / 40000000) := by
  have h := checkLog_sound (w := (2243619879113 / 18243619879113)) (n := 12)
    (lo := (247213519 / 1000000000)) (hi := (3090169 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10243619879113 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10243619879113 / 8000000000000) = 1/(250000000000 / 10243619879113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3712949419 / 1000000000) (148517977 / 40000000) (Real.log (10243619879113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10243619879113 / 250000000000) = -Real.log (250000000000 / 10243619879113) := by
    rw [show ((10243619879113 / 250000000000) : ℝ) = ((250000000000 / 10243619879113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3724928191 / 1000000000) ≤ -Real.log (250000000000 / 10367063744851) ∧
    -Real.log (250000000000 / 10367063744851) ≤ (3724928197 / 1000000000) := by
  have h := checkLog_sound (w := (2367063744851 / 18367063744851)) (n := 12)
    (lo := (259192291 / 1000000000)) (hi := (64798073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10367063744851 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10367063744851 / 8000000000000) = 1/(250000000000 / 10367063744851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3724928191 / 1000000000) (3724928197 / 1000000000) (Real.log (10367063744851 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10367063744851 / 250000000000) = -Real.log (250000000000 / 10367063744851) := by
    rw [show ((10367063744851 / 250000000000) : ℝ) = ((250000000000 / 10367063744851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3697815869 / 1000000000) ≤ -Real.log (62500000000 / 2522441166739) ∧
    -Real.log (62500000000 / 2522441166739) ≤ (29582527 / 8000000) := by
  have h := checkLog_sound (w := (522441166739 / 4522441166739)) (n := 12)
    (lo := (232079969 / 1000000000)) (hi := (23207997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2522441166739 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2522441166739 / 2000000000000) = 1/(62500000000 / 2522441166739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3697815869 / 1000000000) (29582527 / 8000000) (Real.log (2522441166739 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2522441166739 / 62500000000) = -Real.log (62500000000 / 2522441166739) := by
    rw [show ((2522441166739 / 62500000000) : ℝ) = ((62500000000 / 2522441166739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1855025499 / 500000000) ≤ -Real.log (500000000000 / 20427945085073) ∧
    -Real.log (500000000000 / 20427945085073) ≤ (927512751 / 250000000) := by
  have h := checkLog_sound (w := (4427945085073 / 36427945085073)) (n := 12)
    (lo := (122157549 / 500000000)) (hi := (244315099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20427945085073 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20427945085073 / 16000000000000) = 1/(500000000000 / 20427945085073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1855025499 / 500000000) (927512751 / 250000000) (Real.log (20427945085073 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20427945085073 / 500000000000) = -Real.log (500000000000 / 20427945085073) := by
    rw [show ((20427945085073 / 500000000000) : ℝ) = ((500000000000 / 20427945085073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0127

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0128Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0128
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

theorem reflection_log_1_neg : (331515107 / 500000000) ≤ -Real.log (25600 / 49681) ∧
    -Real.log (25600 / 49681) ≤ (132606043 / 200000000) := by
  have h := checkLog_sound (w := (24081 / 75281)) (n := 12)
    (lo := (331515107 / 500000000)) (hi := (132606043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49681 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49681 / 25600) = 1/(25600 / 49681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331515107 / 500000000) (132606043 / 200000000) (Real.log (49681 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49681 / 25600) = -Real.log (25600 / 49681) := by
    rw [show ((49681 / 25600) : ℝ) = ((25600 / 49681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22596321 / 8000000) ≤ -Real.log (1519 / 25600) ∧
    -Real.log (1519 / 25600) ≤ (282454013 / 100000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1519) = 1/(1519 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-282454013 / 100000000) (-22596321 / 8000000) (Real.log (1519 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (662647701 / 1000000000) ≤ -Real.log (12800 / 24831) ∧
    -Real.log (12800 / 24831) ≤ (331323851 / 500000000) := by
  have h := checkLog_sound (w := (12031 / 37631)) (n := 12)
    (lo := (662647701 / 1000000000)) (hi := (331323851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24831 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24831 / 12800) = 1/(12800 / 24831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (662647701 / 1000000000) (331323851 / 500000000) (Real.log (24831 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24831 / 12800) = -Real.log (12800 / 24831) := by
    rw [show ((24831 / 12800) : ℝ) = ((12800 / 24831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1406054739 / 500000000) ≤ -Real.log (769 / 12800) ∧
    -Real.log (769 / 12800) ≤ (2812109483 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 769) = 1/(769 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2812109483 / 1000000000) (-1406054739 / 500000000) (Real.log (769 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78997247 / 125000000) ≤ -Real.log (12800 / 24081) ∧
    -Real.log (12800 / 24081) ≤ (631977977 / 1000000000) := by
  have h := checkLog_sound (w := (11281 / 36881)) (n := 12)
    (lo := (78997247 / 125000000)) (hi := (631977977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24081 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24081 / 12800) = 1/(12800 / 24081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (78997247 / 125000000) (631977977 / 1000000000) (Real.log (24081 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24081 / 12800) = -Real.log (12800 / 24081) := by
    rw [show ((24081 / 12800) : ℝ) = ((12800 / 24081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (426278589 / 200000000) ≤ -Real.log (1519 / 12800) ∧
    -Real.log (1519 / 12800) ≤ (2131392949 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1519) = 1/(1519 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2131392949 / 1000000000) (-426278589 / 200000000) (Real.log (1519 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (631188661 / 1000000000) ≤ -Real.log (6400 / 12031) ∧
    -Real.log (6400 / 12031) ≤ (315594331 / 500000000) := by
  have h := checkLog_sound (w := (5631 / 18431)) (n := 12)
    (lo := (631188661 / 1000000000)) (hi := (315594331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12031 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12031 / 6400) = 1/(6400 / 12031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (631188661 / 1000000000) (315594331 / 500000000) (Real.log (12031 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12031 / 6400) = -Real.log (6400 / 12031) := by
    rw [show ((12031 / 6400) : ℝ) = ((6400 / 12031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1059481149 / 500000000) ≤ -Real.log (769 / 6400) ∧
    -Real.log (769 / 6400) ≤ (1059481151 / 500000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 769) = 1/(769 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1059481151 / 500000000) (-1059481149 / 500000000) (Real.log (769 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (668752023 / 1000000000) ≤ -Real.log (5000 / 9759) ∧
    -Real.log (5000 / 9759) ≤ (83594003 / 125000000) := by
  have h := checkLog_sound (w := (4759 / 14759)) (n := 12)
    (lo := (668752023 / 1000000000)) (hi := (83594003 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9759 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9759 / 5000) = 1/(5000 / 9759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (668752023 / 1000000000) (83594003 / 125000000) (Real.log (9759 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (9759 / 5000) = -Real.log (5000 / 9759) := by
    rw [show ((9759 / 5000) : ℝ) = ((5000 / 9759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (606479251 / 200000000) ≤ -Real.log (241 / 5000) ∧
    -Real.log (241 / 5000) ≤ (151619813 / 50000000) := by
  have h := checkLog_sound (w := (143 / 1107)) (n := 12)
    (lo := (51961507 / 200000000)) (hi := (16237971 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 482) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 482) = 1/(241 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151619813 / 50000000) (-606479251 / 200000000) (Real.log (241 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669035311 / 1000000000) ≤ -Real.log (1000000 / 1952353) ∧
    -Real.log (1000000 / 1952353) ≤ (41814707 / 62500000) := by
  have h := checkLog_sound (w := (952353 / 2952353)) (n := 12)
    (lo := (669035311 / 1000000000)) (hi := (41814707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952353 / 1000000) = 1/(1000000 / 1952353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669035311 / 1000000000) (41814707 / 62500000) (Real.log (1952353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1952353 / 1000000) = -Real.log (1000000 / 1952353) := by
    rw [show ((1952353 / 1000000) : ℝ) = ((1000000 / 1952353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3043935607 / 1000000000) ≤ -Real.log (47647 / 1000000) ∧
    -Real.log (47647 / 1000000) ≤ (760983903 / 250000000) := by
  have h := checkLog_sound (w := (14853 / 110147)) (n := 12)
    (lo := (271346887 / 1000000000)) (hi := (33918361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47647) = 1/(47647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-760983903 / 250000000) (-3043935607 / 1000000000) (Real.log (47647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167094613 / 250000000) ≤ -Real.log (1000000 / 1951071) ∧
    -Real.log (1000000 / 1951071) ≤ (668378453 / 1000000000) := by
  have h := checkLog_sound (w := (951071 / 2951071)) (n := 12)
    (lo := (167094613 / 250000000)) (hi := (668378453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951071 / 1000000) = 1/(1000000 / 1951071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167094613 / 250000000) (668378453 / 1000000000) (Real.log (1951071 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1951071 / 1000000) = -Real.log (1000000 / 1951071) := by
    rw [show ((1951071 / 1000000) : ℝ) = ((1000000 / 1951071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3017385009 / 1000000000) ≤ -Real.log (48929 / 1000000) ∧
    -Real.log (48929 / 1000000) ≤ (1508692507 / 500000000) := by
  have h := checkLog_sound (w := (13571 / 111429)) (n := 12)
    (lo := (244796289 / 1000000000)) (hi := (24479629 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48929) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48929) = 1/(48929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1508692507 / 500000000) (-3017385009 / 1000000000) (Real.log (48929 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334336047 / 500000000) ≤ -Real.log (250000 / 487911) ∧
    -Real.log (250000 / 487911) ≤ (133734419 / 200000000) := by
  have h := checkLog_sound (w := (237911 / 737911)) (n := 12)
    (lo := (334336047 / 500000000)) (hi := (133734419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487911 / 250000) = 1/(250000 / 487911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334336047 / 500000000) (133734419 / 200000000) (Real.log (487911 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (487911 / 250000) = -Real.log (250000 / 487911) := by
    rw [show ((487911 / 250000) : ℝ) = ((250000 / 487911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3029164967 / 1000000000) ≤ -Real.log (12089 / 250000) ∧
    -Real.log (12089 / 250000) ≤ (757291243 / 250000000) := by
  have h := checkLog_sound (w := (1768 / 13857)) (n := 12)
    (lo := (256576247 / 1000000000)) (hi := (32072031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12089) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12089) = 1/(12089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-757291243 / 250000000) (-3029164967 / 1000000000) (Real.log (12089 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1850574139 / 500000000) ≤ -Real.log (125000000000 / 5061721991701) ∧
    -Real.log (125000000000 / 5061721991701) ≤ (925287071 / 250000000) := by
  have h := checkLog_sound (w := (1061721991701 / 9061721991701)) (n := 12)
    (lo := (117706189 / 500000000)) (hi := (235412379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5061721991701 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5061721991701 / 4000000000000) = 1/(125000000000 / 5061721991701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1850574139 / 500000000) (925287071 / 250000000) (Real.log (5061721991701 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5061721991701 / 125000000000) = -Real.log (125000000000 / 5061721991701) := by
    rw [show ((5061721991701 / 125000000000) : ℝ) = ((125000000000 / 5061721991701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1856485459 / 500000000) ≤ -Real.log (62500000000 / 2560960028963) ∧
    -Real.log (62500000000 / 2560960028963) ≤ (928242731 / 250000000) := by
  have h := checkLog_sound (w := (560960028963 / 4560960028963)) (n := 12)
    (lo := (123617509 / 500000000)) (hi := (247235019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560960028963 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2560960028963 / 2000000000000) = 1/(62500000000 / 2560960028963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1856485459 / 500000000) (928242731 / 250000000) (Real.log (2560960028963 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2560960028963 / 62500000000) = -Real.log (62500000000 / 2560960028963) := by
    rw [show ((2560960028963 / 62500000000) : ℝ) = ((62500000000 / 2560960028963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3685763461 / 1000000000) ≤ -Real.log (500000000000 / 19937777187353) ∧
    -Real.log (500000000000 / 19937777187353) ≤ (3685763467 / 1000000000) := by
  have h := checkLog_sound (w := (3937777187353 / 35937777187353)) (n := 12)
    (lo := (220027561 / 1000000000)) (hi := (110013781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19937777187353 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19937777187353 / 16000000000000) = 1/(500000000000 / 19937777187353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3685763461 / 1000000000) (3685763467 / 1000000000) (Real.log (19937777187353 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19937777187353 / 500000000000) = -Real.log (500000000000 / 19937777187353) := by
    rw [show ((19937777187353 / 500000000000) : ℝ) = ((500000000000 / 19937777187353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3697837061 / 1000000000) ≤ -Real.log (50000000000 / 2017995698569) ∧
    -Real.log (50000000000 / 2017995698569) ≤ (3697837067 / 1000000000) := by
  have h := checkLog_sound (w := (417995698569 / 3617995698569)) (n := 12)
    (lo := (232101161 / 1000000000)) (hi := (116050581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017995698569 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2017995698569 / 1600000000000) = 1/(50000000000 / 2017995698569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3697837061 / 1000000000) (3697837067 / 1000000000) (Real.log (2017995698569 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2017995698569 / 50000000000) = -Real.log (50000000000 / 2017995698569) := by
    rw [show ((2017995698569 / 50000000000) : ℝ) = ((50000000000 / 2017995698569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0128

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0129Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0129
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

theorem reflection_log_1_neg : (662647701 / 1000000000) ≤ -Real.log (12800 / 24831) ∧
    -Real.log (12800 / 24831) ≤ (331323851 / 500000000) := by
  have h := checkLog_sound (w := (12031 / 37631)) (n := 12)
    (lo := (662647701 / 1000000000)) (hi := (331323851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24831 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24831 / 12800) = 1/(12800 / 24831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (662647701 / 1000000000) (331323851 / 500000000) (Real.log (24831 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24831 / 12800) = -Real.log (12800 / 24831) := by
    rw [show ((24831 / 12800) : ℝ) = ((12800 / 24831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1406054739 / 500000000) ≤ -Real.log (769 / 12800) ∧
    -Real.log (769 / 12800) ≤ (2812109483 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 769) = 1/(769 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2812109483 / 1000000000) (-1406054739 / 500000000) (Real.log (769 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331132521 / 500000000) ≤ -Real.log (25600 / 49643) ∧
    -Real.log (25600 / 49643) ≤ (662265043 / 1000000000) := by
  have h := checkLog_sound (w := (24043 / 75243)) (n := 12)
    (lo := (331132521 / 500000000)) (hi := (662265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49643 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49643 / 25600) = 1/(25600 / 49643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331132521 / 500000000) (662265043 / 1000000000) (Real.log (49643 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49643 / 25600) = -Real.log (25600 / 49643) := by
    rw [show ((49643 / 25600) : ℝ) = ((25600 / 49643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (87494733 / 31250000) ≤ -Real.log (1557 / 25600) ∧
    -Real.log (1557 / 25600) ≤ (2799831461 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1557) = 1/(1557 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2799831461 / 1000000000) (-87494733 / 31250000) (Real.log (1557 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (631188661 / 1000000000) ≤ -Real.log (6400 / 12031) ∧
    -Real.log (6400 / 12031) ≤ (315594331 / 500000000) := by
  have h := checkLog_sound (w := (5631 / 18431)) (n := 12)
    (lo := (631188661 / 1000000000)) (hi := (315594331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12031 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12031 / 6400) = 1/(6400 / 12031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (631188661 / 1000000000) (315594331 / 500000000) (Real.log (12031 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12031 / 6400) = -Real.log (6400 / 12031) := by
    rw [show ((12031 / 6400) : ℝ) = ((6400 / 12031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1059481149 / 500000000) ≤ -Real.log (769 / 6400) ∧
    -Real.log (769 / 6400) ≤ (1059481151 / 500000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 769) = 1/(769 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1059481151 / 500000000) (-1059481149 / 500000000) (Real.log (769 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (315199361 / 500000000) ≤ -Real.log (12800 / 24043) ∧
    -Real.log (12800 / 24043) ≤ (630398723 / 1000000000) := by
  have h := checkLog_sound (w := (11243 / 36843)) (n := 12)
    (lo := (315199361 / 500000000)) (hi := (630398723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24043 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24043 / 12800) = 1/(12800 / 24043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (315199361 / 500000000) (630398723 / 1000000000) (Real.log (24043 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24043 / 12800) = -Real.log (12800 / 24043) := by
    rw [show ((24043 / 12800) : ℝ) = ((12800 / 24043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (526671069 / 250000000) ≤ -Real.log (1557 / 12800) ∧
    -Real.log (1557 / 12800) ≤ (52667107 / 25000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1557) = 1/(1557 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52667107 / 25000000) (-526671069 / 250000000) (Real.log (1557 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8355871 / 12500000) ≤ -Real.log (1000000 / 1951249) ∧
    -Real.log (1000000 / 1951249) ≤ (668469681 / 1000000000) := by
  have h := checkLog_sound (w := (951249 / 2951249)) (n := 12)
    (lo := (8355871 / 12500000)) (hi := (668469681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951249 / 1000000) = 1/(1000000 / 1951249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8355871 / 12500000) (668469681 / 1000000000) (Real.log (1951249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1951249 / 1000000) = -Real.log (1000000 / 1951249) := by
    rw [show ((1951249 / 1000000) : ℝ) = ((1000000 / 1951249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1510514783 / 500000000) ≤ -Real.log (48751 / 1000000) ∧
    -Real.log (48751 / 1000000) ≤ (3021029571 / 1000000000) := by
  have h := checkLog_sound (w := (13749 / 111251)) (n := 12)
    (lo := (124220423 / 500000000)) (hi := (248440847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48751) = 1/(48751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3021029571 / 1000000000) (-1510514783 / 500000000) (Real.log (48751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83594067 / 125000000) ≤ -Real.log (1000000 / 1951801) ∧
    -Real.log (1000000 / 1951801) ≤ (668752537 / 1000000000) := by
  have h := checkLog_sound (w := (951801 / 2951801)) (n := 12)
    (lo := (83594067 / 125000000)) (hi := (668752537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951801 / 1000000) = 1/(1000000 / 1951801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83594067 / 125000000) (668752537 / 1000000000) (Real.log (1951801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1951801 / 1000000) = -Real.log (1000000 / 1951801) := by
    rw [show ((1951801 / 1000000) : ℝ) = ((1000000 / 1951801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1516208501 / 500000000) ≤ -Real.log (48199 / 1000000) ∧
    -Real.log (48199 / 1000000) ≤ (3032417007 / 1000000000) := by
  have h := checkLog_sound (w := (14301 / 110699)) (n := 12)
    (lo := (129914141 / 500000000)) (hi := (259828283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48199) = 1/(48199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3032417007 / 1000000000) (-1516208501 / 500000000) (Real.log (48199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668085237 / 1000000000) ≤ -Real.log (1000000 / 1950499) ∧
    -Real.log (1000000 / 1950499) ≤ (334042619 / 500000000) := by
  have h := checkLog_sound (w := (950499 / 2950499)) (n := 12)
    (lo := (668085237 / 1000000000)) (hi := (334042619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950499 / 1000000) = 1/(1000000 / 1950499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668085237 / 1000000000) (334042619 / 500000000) (Real.log (1950499 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1950499 / 1000000) = -Real.log (1000000 / 1950499) := by
    rw [show ((1950499 / 1000000) : ℝ) = ((1000000 / 1950499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601152481 / 200000000) ≤ -Real.log (49501 / 1000000) ∧
    -Real.log (49501 / 1000000) ≤ (300576241 / 100000000) := by
  have h := checkLog_sound (w := (12999 / 112001)) (n := 12)
    (lo := (46634737 / 200000000)) (hi := (116586843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49501) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49501) = 1/(49501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300576241 / 100000000) (-601152481 / 200000000) (Real.log (49501 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (133675793 / 200000000) ≤ -Real.log (31250 / 60971) ∧
    -Real.log (31250 / 60971) ≤ (334189483 / 500000000) := by
  have h := checkLog_sound (w := (29721 / 92221)) (n := 12)
    (lo := (133675793 / 200000000)) (hi := (334189483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60971 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60971 / 31250) = 1/(31250 / 60971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (133675793 / 200000000) (334189483 / 500000000) (Real.log (60971 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (60971 / 31250) = -Real.log (31250 / 60971) := by
    rw [show ((60971 / 31250) : ℝ) = ((31250 / 60971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1508702723 / 500000000) ≤ -Real.log (1529 / 31250) ∧
    -Real.log (1529 / 31250) ≤ (3017405451 / 1000000000) := by
  have h := checkLog_sound (w := (3393 / 27857)) (n := 12)
    (lo := (122408363 / 500000000)) (hi := (244816727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12232) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12232) = 1/(1529 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3017405451 / 1000000000) (-1508702723 / 500000000) (Real.log (1529 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1844749623 / 500000000) ≤ -Real.log (250000000000 / 10006199872823) ∧
    -Real.log (250000000000 / 10006199872823) ≤ (922374813 / 250000000) := by
  have h := checkLog_sound (w := (2006199872823 / 18006199872823)) (n := 12)
    (lo := (111881673 / 500000000)) (hi := (223763347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10006199872823 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10006199872823 / 8000000000000) = 1/(250000000000 / 10006199872823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1844749623 / 500000000) (922374813 / 250000000) (Real.log (10006199872823 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10006199872823 / 250000000000) = -Real.log (250000000000 / 10006199872823) := by
    rw [show ((10006199872823 / 250000000000) : ℝ) = ((250000000000 / 10006199872823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1850584769 / 500000000) ≤ -Real.log (62500000000 / 2530914801137) ∧
    -Real.log (62500000000 / 2530914801137) ≤ (462646193 / 125000000) := by
  have h := checkLog_sound (w := (530914801137 / 4530914801137)) (n := 12)
    (lo := (117716819 / 500000000)) (hi := (235433639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2530914801137 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2530914801137 / 2000000000000) = 1/(62500000000 / 2530914801137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1850584769 / 500000000) (462646193 / 125000000) (Real.log (2530914801137 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2530914801137 / 62500000000) = -Real.log (62500000000 / 2530914801137) := by
    rw [show ((2530914801137 / 62500000000) : ℝ) = ((62500000000 / 2530914801137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1836923821 / 500000000) ≤ -Real.log (125000000000 / 4925403022161) ∧
    -Real.log (125000000000 / 4925403022161) ≤ (114807739 / 31250000) := by
  have h := checkLog_sound (w := (925403022161 / 8925403022161)) (n := 12)
    (lo := (104055871 / 500000000)) (hi := (208111743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4925403022161 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4925403022161 / 4000000000000) = 1/(125000000000 / 4925403022161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1836923821 / 500000000) (114807739 / 31250000) (Real.log (4925403022161 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4925403022161 / 125000000000) = -Real.log (125000000000 / 4925403022161) := by
    rw [show ((4925403022161 / 125000000000) : ℝ) = ((125000000000 / 4925403022161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3685784411 / 1000000000) ≤ -Real.log (500000000000 / 19938194898627) ∧
    -Real.log (500000000000 / 19938194898627) ≤ (3685784417 / 1000000000) := by
  have h := checkLog_sound (w := (3938194898627 / 35938194898627)) (n := 12)
    (lo := (220048511 / 1000000000)) (hi := (1719129 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19938194898627 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19938194898627 / 16000000000000) = 1/(500000000000 / 19938194898627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3685784411 / 1000000000) (3685784417 / 1000000000) (Real.log (19938194898627 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19938194898627 / 500000000000) = -Real.log (500000000000 / 19938194898627) := by
    rw [show ((19938194898627 / 500000000000) : ℝ) = ((500000000000 / 19938194898627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0129

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0130Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0130
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

theorem reflection_log_1_neg : (331132521 / 500000000) ≤ -Real.log (25600 / 49643) ∧
    -Real.log (25600 / 49643) ≤ (662265043 / 1000000000) := by
  have h := checkLog_sound (w := (24043 / 75243)) (n := 12)
    (lo := (331132521 / 500000000)) (hi := (662265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49643 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49643 / 25600) = 1/(25600 / 49643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331132521 / 500000000) (662265043 / 1000000000) (Real.log (49643 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49643 / 25600) = -Real.log (25600 / 49643) := by
    rw [show ((49643 / 25600) : ℝ) = ((25600 / 49643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (87494733 / 31250000) ≤ -Real.log (1557 / 25600) ∧
    -Real.log (1557 / 25600) ≤ (2799831461 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1557) = 1/(1557 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2799831461 / 1000000000) (-87494733 / 31250000) (Real.log (1557 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (165470559 / 250000000) ≤ -Real.log (3200 / 6203) ∧
    -Real.log (3200 / 6203) ≤ (661882237 / 1000000000) := by
  have h := checkLog_sound (w := (3003 / 9403)) (n := 12)
    (lo := (165470559 / 250000000)) (hi := (661882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6203 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6203 / 3200) = 1/(3200 / 6203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (165470559 / 250000000) (661882237 / 1000000000) (Real.log (6203 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6203 / 3200) = -Real.log (3200 / 6203) := by
    rw [show ((6203 / 3200) : ℝ) = ((3200 / 6203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2787702357 / 1000000000) ≤ -Real.log (197 / 3200) ∧
    -Real.log (197 / 3200) ≤ (1393851181 / 500000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 197) = 1/(197 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1393851181 / 500000000) (-2787702357 / 1000000000) (Real.log (197 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (315199361 / 500000000) ≤ -Real.log (12800 / 24043) ∧
    -Real.log (12800 / 24043) ≤ (630398723 / 1000000000) := by
  have h := checkLog_sound (w := (11243 / 36843)) (n := 12)
    (lo := (315199361 / 500000000)) (hi := (630398723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24043 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24043 / 12800) = 1/(12800 / 24043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (315199361 / 500000000) (630398723 / 1000000000) (Real.log (24043 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24043 / 12800) = -Real.log (12800 / 24043) := by
    rw [show ((24043 / 12800) : ℝ) = ((12800 / 24043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (526671069 / 250000000) ≤ -Real.log (1557 / 12800) ∧
    -Real.log (1557 / 12800) ≤ (52667107 / 25000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1557) = 1/(1557 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52667107 / 25000000) (-526671069 / 250000000) (Real.log (1557 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (629608159 / 1000000000) ≤ -Real.log (1600 / 3003) ∧
    -Real.log (1600 / 3003) ≤ (3935051 / 6250000) := by
  have h := checkLog_sound (w := (1403 / 4603)) (n := 12)
    (lo := (629608159 / 1000000000)) (hi := (3935051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3003 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3003 / 1600) = 1/(1600 / 3003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (629608159 / 1000000000) (3935051 / 6250000) (Real.log (3003 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3003 / 1600) = -Real.log (1600 / 3003) := by
    rw [show ((3003 / 1600) : ℝ) = ((1600 / 3003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2094555177 / 1000000000) ≤ -Real.log (197 / 1600) ∧
    -Real.log (197 / 1600) ≤ (2094555181 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 197) = 1/(197 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2094555181 / 1000000000) (-2094555177 / 1000000000) (Real.log (197 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (668187769 / 1000000000) ≤ -Real.log (1000000 / 1950699) ∧
    -Real.log (1000000 / 1950699) ≤ (66818777 / 100000000) := by
  have h := checkLog_sound (w := (950699 / 2950699)) (n := 12)
    (lo := (668187769 / 1000000000)) (hi := (66818777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950699 / 1000000) = 1/(1000000 / 1950699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (668187769 / 1000000000) (66818777 / 100000000) (Real.log (1950699 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1950699 / 1000000) = -Real.log (1000000 / 1950699) := by
    rw [show ((1950699 / 1000000) : ℝ) = ((1000000 / 1950699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3009810911 / 1000000000) ≤ -Real.log (49301 / 1000000) ∧
    -Real.log (49301 / 1000000) ≤ (752452729 / 250000000) := by
  have h := checkLog_sound (w := (13199 / 111801)) (n := 12)
    (lo := (237222191 / 1000000000)) (hi := (14826387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49301) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49301) = 1/(49301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-752452729 / 250000000) (-3009810911 / 1000000000) (Real.log (49301 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41779387 / 62500000) ≤ -Real.log (800 / 1561) ∧
    -Real.log (800 / 1561) ≤ (668470193 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 2361)) (n := 12)
    (lo := (41779387 / 62500000)) (hi := (668470193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1561 / 800) = 1/(800 / 1561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41779387 / 62500000) (668470193 / 1000000000) (Real.log (1561 / 800)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1561 / 800) = -Real.log (800 / 1561) := by
    rw [show ((1561 / 800) : ℝ) = ((800 / 1561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3021050079 / 1000000000) ≤ -Real.log (39 / 800) ∧
    -Real.log (39 / 800) ≤ (755262521 / 250000000) := by
  have h := checkLog_sound (w := (11 / 89)) (n := 12)
    (lo := (248461359 / 1000000000)) (hi := (3105767 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(50 / 39) = 1/(39 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-755262521 / 250000000) (-3021050079 / 1000000000) (Real.log (39 / 800)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10434257 / 15625000) ≤ -Real.log (125000 / 243741) ∧
    -Real.log (125000 / 243741) ≤ (667792449 / 1000000000) := by
  have h := checkLog_sound (w := (118741 / 368741)) (n := 12)
    (lo := (10434257 / 15625000)) (hi := (667792449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243741 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243741 / 125000) = 1/(125000 / 243741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10434257 / 15625000) (667792449 / 1000000000) (Real.log (243741 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243741 / 125000) = -Real.log (125000 / 243741) := by
    rw [show ((243741 / 125000) : ℝ) = ((125000 / 243741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2994293307 / 1000000000) ≤ -Real.log (6259 / 125000) ∧
    -Real.log (6259 / 125000) ≤ (46785833 / 15625000) := by
  have h := checkLog_sound (w := (3107 / 28143)) (n := 12)
    (lo := (221704587 / 1000000000)) (hi := (55426147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12518) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12518) = 1/(6259 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46785833 / 15625000) (-2994293307 / 1000000000) (Real.log (6259 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (668085749 / 1000000000) ≤ -Real.log (2000 / 3901) ∧
    -Real.log (2000 / 3901) ≤ (2672343 / 4000000) := by
  have h := checkLog_sound (w := (1901 / 5901)) (n := 12)
    (lo := (668085749 / 1000000000)) (hi := (2672343 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3901 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3901 / 2000) = 1/(2000 / 3901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (668085749 / 1000000000) (2672343 / 4000000) (Real.log (3901 / 2000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (3901 / 2000) = -Real.log (2000 / 3901) := by
    rw [show ((3901 / 2000) : ℝ) = ((2000 / 3901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3005782607 / 1000000000) ≤ -Real.log (99 / 2000) ∧
    -Real.log (99 / 2000) ≤ (751445653 / 250000000) := by
  have h := checkLog_sound (w := (13 / 112)) (n := 12)
    (lo := (233193887 / 1000000000)) (hi := (7287309 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 99) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 99) = 1/(99 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-751445653 / 250000000) (-3005782607 / 1000000000) (Real.log (99 / 2000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3677998681 / 1000000000) ≤ -Real.log (250000000000 / 9891782113953) ∧
    -Real.log (250000000000 / 9891782113953) ≤ (3677998687 / 1000000000) := by
  have h := checkLog_sound (w := (1891782113953 / 17891782113953)) (n := 12)
    (lo := (212262781 / 1000000000)) (hi := (106131391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9891782113953 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9891782113953 / 8000000000000) = 1/(250000000000 / 9891782113953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3677998681 / 1000000000) (3677998687 / 1000000000) (Real.log (9891782113953 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9891782113953 / 250000000000) = -Real.log (250000000000 / 9891782113953) := by
    rw [show ((9891782113953 / 250000000000) : ℝ) = ((250000000000 / 9891782113953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3689520271 / 1000000000) ≤ -Real.log (500000000000 / 20012820512821) ∧
    -Real.log (500000000000 / 20012820512821) ≤ (3689520277 / 1000000000) := by
  have h := checkLog_sound (w := (4012820512821 / 36012820512821)) (n := 12)
    (lo := (223784371 / 1000000000)) (hi := (55946093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20012820512821 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20012820512821 / 16000000000000) = 1/(500000000000 / 20012820512821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3689520271 / 1000000000) (3689520277 / 1000000000) (Real.log (20012820512821 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20012820512821 / 500000000000) = -Real.log (500000000000 / 20012820512821) := by
    rw [show ((20012820512821 / 500000000000) : ℝ) = ((500000000000 / 20012820512821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (732417151 / 200000000) ≤ -Real.log (250000000000 / 9735620706183) ∧
    -Real.log (250000000000 / 9735620706183) ≤ (3662085761 / 1000000000) := by
  have h := checkLog_sound (w := (1735620706183 / 17735620706183)) (n := 12)
    (lo := (39269971 / 200000000)) (hi := (6135933 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9735620706183 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9735620706183 / 8000000000000) = 1/(250000000000 / 9735620706183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (732417151 / 200000000) (3662085761 / 1000000000) (Real.log (9735620706183 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9735620706183 / 250000000000) = -Real.log (250000000000 / 9735620706183) := by
    rw [show ((9735620706183 / 250000000000) : ℝ) = ((250000000000 / 9735620706183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (918467089 / 250000000) ≤ -Real.log (500000000000 / 19702020202021) ∧
    -Real.log (500000000000 / 19702020202021) ≤ (1836934181 / 500000000) := by
  have h := checkLog_sound (w := (3702020202021 / 35702020202021)) (n := 12)
    (lo := (26016557 / 125000000)) (hi := (208132457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19702020202021 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19702020202021 / 16000000000000) = 1/(500000000000 / 19702020202021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (918467089 / 250000000) (1836934181 / 500000000) (Real.log (19702020202021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19702020202021 / 500000000000) = -Real.log (500000000000 / 19702020202021) := by
    rw [show ((19702020202021 / 500000000000) : ℝ) = ((500000000000 / 19702020202021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0130

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0131Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0131
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

theorem reflection_log_1_neg : (165470559 / 250000000) ≤ -Real.log (3200 / 6203) ∧
    -Real.log (3200 / 6203) ≤ (661882237 / 1000000000) := by
  have h := checkLog_sound (w := (3003 / 9403)) (n := 12)
    (lo := (165470559 / 250000000)) (hi := (661882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6203 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6203 / 3200) = 1/(3200 / 6203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (165470559 / 250000000) (661882237 / 1000000000) (Real.log (6203 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6203 / 3200) = -Real.log (3200 / 6203) := by
    rw [show ((6203 / 3200) : ℝ) = ((3200 / 6203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2787702357 / 1000000000) ≤ -Real.log (197 / 3200) ∧
    -Real.log (197 / 3200) ≤ (1393851181 / 500000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 197) = 1/(197 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1393851181 / 500000000) (-2787702357 / 1000000000) (Real.log (197 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (661499283 / 1000000000) ≤ -Real.log (5120 / 9921) ∧
    -Real.log (5120 / 9921) ≤ (165374821 / 250000000) := by
  have h := checkLog_sound (w := (4801 / 15041)) (n := 12)
    (lo := (661499283 / 1000000000)) (hi := (165374821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9921 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9921 / 5120) = 1/(5120 / 9921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (661499283 / 1000000000) (165374821 / 250000000) (Real.log (9921 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9921 / 5120) = -Real.log (5120 / 9921) := by
    rw [show ((9921 / 5120) : ℝ) = ((5120 / 9921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2775718613 / 1000000000) ≤ -Real.log (319 / 5120) ∧
    -Real.log (319 / 5120) ≤ (1387859309 / 500000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 319) = 1/(319 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1387859309 / 500000000) (-2775718613 / 1000000000) (Real.log (319 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (629608159 / 1000000000) ≤ -Real.log (1600 / 3003) ∧
    -Real.log (1600 / 3003) ≤ (3935051 / 6250000) := by
  have h := checkLog_sound (w := (1403 / 4603)) (n := 12)
    (lo := (629608159 / 1000000000)) (hi := (3935051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3003 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3003 / 1600) = 1/(1600 / 3003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (629608159 / 1000000000) (3935051 / 6250000) (Real.log (3003 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3003 / 1600) = -Real.log (1600 / 3003) := by
    rw [show ((3003 / 1600) : ℝ) = ((1600 / 3003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2094555177 / 1000000000) ≤ -Real.log (197 / 1600) ∧
    -Real.log (197 / 1600) ≤ (2094555181 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 197) = 1/(197 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2094555181 / 1000000000) (-2094555177 / 1000000000) (Real.log (197 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (628816971 / 1000000000) ≤ -Real.log (2560 / 4801) ∧
    -Real.log (2560 / 4801) ≤ (157204243 / 250000000) := by
  have h := checkLog_sound (w := (2241 / 7361)) (n := 12)
    (lo := (628816971 / 1000000000)) (hi := (157204243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 2560) = 1/(2560 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (628816971 / 1000000000) (157204243 / 250000000) (Real.log (4801 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4801 / 2560) = -Real.log (2560 / 4801) := by
    rw [show ((4801 / 2560) : ℝ) = ((2560 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2082571433 / 1000000000) ≤ -Real.log (319 / 2560) ∧
    -Real.log (319 / 2560) ≤ (2082571437 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 319) = 1/(319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2082571437 / 1000000000) (-2082571433 / 1000000000) (Real.log (319 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166976573 / 250000000) ≤ -Real.log (20000 / 39003) ∧
    -Real.log (20000 / 39003) ≤ (667906293 / 1000000000) := by
  have h := checkLog_sound (w := (19003 / 59003)) (n := 12)
    (lo := (166976573 / 250000000)) (hi := (667906293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39003 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39003 / 20000) = 1/(20000 / 39003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166976573 / 250000000) (667906293 / 1000000000) (Real.log (39003 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (39003 / 20000) = -Real.log (20000 / 39003) := by
    rw [show ((39003 / 20000) : ℝ) = ((20000 / 39003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149936839 / 50000000) ≤ -Real.log (997 / 20000) ∧
    -Real.log (997 / 20000) ≤ (599747357 / 200000000) := by
  have h := checkLog_sound (w := (253 / 2247)) (n := 12)
    (lo := (11307403 / 50000000)) (hi := (226148061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 997) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1250 / 997) = 1/(997 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-599747357 / 200000000) (-149936839 / 50000000) (Real.log (997 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334094141 / 500000000) ≤ -Real.log (10000 / 19507) ∧
    -Real.log (10000 / 19507) ≤ (668188283 / 1000000000) := by
  have h := checkLog_sound (w := (9507 / 29507)) (n := 12)
    (lo := (334094141 / 500000000)) (hi := (668188283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19507 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19507 / 10000) = 1/(10000 / 19507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334094141 / 500000000) (668188283 / 1000000000) (Real.log (19507 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19507 / 10000) = -Real.log (10000 / 19507) := by
    rw [show ((19507 / 10000) : ℝ) = ((10000 / 19507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (601966239 / 200000000) ≤ -Real.log (493 / 10000) ∧
    -Real.log (493 / 10000) ≤ (3762289 / 1250000) := by
  have h := checkLog_sound (w := (66 / 559)) (n := 12)
    (lo := (9489699 / 40000000)) (hi := (59310619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 493) = 1/(493 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3762289 / 1250000) (-601966239 / 200000000) (Real.log (493 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (333749787 / 500000000) ≤ -Real.log (1000000 / 1949357) ∧
    -Real.log (1000000 / 1949357) ≤ (26699983 / 40000000) := by
  have h := checkLog_sound (w := (949357 / 2949357)) (n := 12)
    (lo := (333749787 / 500000000)) (hi := (26699983 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949357 / 1000000) = 1/(1000000 / 1949357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (333749787 / 500000000) (26699983 / 40000000) (Real.log (1949357 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1949357 / 1000000) = -Real.log (1000000 / 1949357) := by
    rw [show ((1949357 / 1000000) : ℝ) = ((1000000 / 1949357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1491477129 / 500000000) ≤ -Real.log (50643 / 1000000) ∧
    -Real.log (50643 / 1000000) ≤ (2982954263 / 1000000000) := by
  have h := checkLog_sound (w := (11857 / 113143)) (n := 12)
    (lo := (105182769 / 500000000)) (hi := (210365539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50643) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50643) = 1/(50643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2982954263 / 1000000000) (-1491477129 / 500000000) (Real.log (50643 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (667792961 / 1000000000) ≤ -Real.log (1000000 / 1949929) ∧
    -Real.log (1000000 / 1949929) ≤ (333896481 / 500000000) := by
  have h := checkLog_sound (w := (949929 / 2949929)) (n := 12)
    (lo := (667792961 / 1000000000)) (hi := (333896481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949929 / 1000000) = 1/(1000000 / 1949929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (667792961 / 1000000000) (333896481 / 500000000) (Real.log (1949929 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1949929 / 1000000) = -Real.log (1000000 / 1949929) := by
    rw [show ((1949929 / 1000000) : ℝ) = ((1000000 / 1949929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1497156639 / 500000000) ≤ -Real.log (50071 / 1000000) ∧
    -Real.log (50071 / 1000000) ≤ (2994313283 / 1000000000) := by
  have h := checkLog_sound (w := (12429 / 112571)) (n := 12)
    (lo := (110862279 / 500000000)) (hi := (221724559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50071) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50071) = 1/(50071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2994313283 / 1000000000) (-1497156639 / 500000000) (Real.log (50071 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (28645649 / 7812500) ≤ -Real.log (62500000000 / 2445022567703) ∧
    -Real.log (62500000000 / 2445022567703) ≤ (1833321539 / 500000000) := by
  have h := checkLog_sound (w := (445022567703 / 4445022567703)) (n := 12)
    (lo := (50226793 / 250000000)) (hi := (200907173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2445022567703 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2445022567703 / 2000000000000) = 1/(62500000000 / 2445022567703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28645649 / 7812500) (1833321539 / 500000000) (Real.log (2445022567703 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2445022567703 / 62500000000) = -Real.log (62500000000 / 2445022567703) := by
    rw [show ((2445022567703 / 62500000000) : ℝ) = ((62500000000 / 2445022567703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3678019477 / 1000000000) ≤ -Real.log (50000000000 / 1978397565923) ∧
    -Real.log (50000000000 / 1978397565923) ≤ (3678019483 / 1000000000) := by
  have h := checkLog_sound (w := (378397565923 / 3578397565923)) (n := 12)
    (lo := (212283577 / 1000000000)) (hi := (106141789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978397565923 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1978397565923 / 1600000000000) = 1/(50000000000 / 1978397565923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3678019477 / 1000000000) (3678019483 / 1000000000) (Real.log (1978397565923 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1978397565923 / 50000000000) = -Real.log (50000000000 / 1978397565923) := by
    rw [show ((1978397565923 / 50000000000) : ℝ) = ((50000000000 / 1978397565923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3650453833 / 1000000000) ≤ -Real.log (500000000000 / 19246065596429) ∧
    -Real.log (500000000000 / 19246065596429) ≤ (3650453839 / 1000000000) := by
  have h := checkLog_sound (w := (3246065596429 / 35246065596429)) (n := 12)
    (lo := (184717933 / 1000000000)) (hi := (92358967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19246065596429 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19246065596429 / 16000000000000) = 1/(500000000000 / 19246065596429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3650453833 / 1000000000) (3650453839 / 1000000000) (Real.log (19246065596429 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19246065596429 / 500000000000) = -Real.log (500000000000 / 19246065596429) := by
    rw [show ((19246065596429 / 500000000000) : ℝ) = ((500000000000 / 19246065596429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3662106239 / 1000000000) ≤ -Real.log (15625000000 / 608488758463) ∧
    -Real.log (15625000000 / 608488758463) ≤ (732421249 / 200000000) := by
  have h := checkLog_sound (w := (108488758463 / 1108488758463)) (n := 12)
    (lo := (196370339 / 1000000000)) (hi := (9818517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608488758463 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(608488758463 / 500000000000) = 1/(15625000000 / 608488758463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3662106239 / 1000000000) (732421249 / 200000000) (Real.log (608488758463 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (608488758463 / 15625000000) = -Real.log (15625000000 / 608488758463) := by
    rw [show ((608488758463 / 15625000000) : ℝ) = ((15625000000 / 608488758463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0131

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0132Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0132
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

theorem reflection_log_1_neg : (661499283 / 1000000000) ≤ -Real.log (5120 / 9921) ∧
    -Real.log (5120 / 9921) ≤ (165374821 / 250000000) := by
  have h := checkLog_sound (w := (4801 / 15041)) (n := 12)
    (lo := (661499283 / 1000000000)) (hi := (165374821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9921 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9921 / 5120) = 1/(5120 / 9921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (661499283 / 1000000000) (165374821 / 250000000) (Real.log (9921 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9921 / 5120) = -Real.log (5120 / 9921) := by
    rw [show ((9921 / 5120) : ℝ) = ((5120 / 9921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2775718613 / 1000000000) ≤ -Real.log (319 / 5120) ∧
    -Real.log (319 / 5120) ≤ (1387859309 / 500000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 319) = 1/(319 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1387859309 / 500000000) (-2775718613 / 1000000000) (Real.log (319 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82639523 / 125000000) ≤ -Real.log (12800 / 24793) ∧
    -Real.log (12800 / 24793) ≤ (132223237 / 200000000) := by
  have h := checkLog_sound (w := (11993 / 37593)) (n := 12)
    (lo := (82639523 / 125000000)) (hi := (132223237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24793 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24793 / 12800) = 1/(12800 / 24793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82639523 / 125000000) (132223237 / 200000000) (Real.log (24793 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24793 / 12800) = -Real.log (12800 / 24793) := by
    rw [show ((24793 / 12800) : ℝ) = ((12800 / 24793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2763876779 / 1000000000) ≤ -Real.log (807 / 12800) ∧
    -Real.log (807 / 12800) ≤ (2763876783 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 807) = 1/(807 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2763876783 / 1000000000) (-2763876779 / 1000000000) (Real.log (807 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (628816971 / 1000000000) ≤ -Real.log (2560 / 4801) ∧
    -Real.log (2560 / 4801) ≤ (157204243 / 250000000) := by
  have h := checkLog_sound (w := (2241 / 7361)) (n := 12)
    (lo := (628816971 / 1000000000)) (hi := (157204243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 2560) = 1/(2560 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (628816971 / 1000000000) (157204243 / 250000000) (Real.log (4801 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4801 / 2560) = -Real.log (2560 / 4801) := by
    rw [show ((4801 / 2560) : ℝ) = ((2560 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2082571433 / 1000000000) ≤ -Real.log (319 / 2560) ∧
    -Real.log (319 / 2560) ≤ (2082571437 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 319) = 1/(319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2082571437 / 1000000000) (-2082571433 / 1000000000) (Real.log (319 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125605031 / 200000000) ≤ -Real.log (6400 / 11993) ∧
    -Real.log (6400 / 11993) ≤ (157006289 / 250000000) := by
  have h := checkLog_sound (w := (5593 / 18393)) (n := 12)
    (lo := (125605031 / 200000000)) (hi := (157006289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 6400) = 1/(6400 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125605031 / 200000000) (157006289 / 250000000) (Real.log (11993 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11993 / 6400) = -Real.log (6400 / 11993) := by
    rw [show ((11993 / 6400) : ℝ) = ((6400 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2070729599 / 1000000000) ≤ -Real.log (807 / 6400) ∧
    -Real.log (807 / 6400) ≤ (1035364801 / 500000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 807) = 1/(807 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1035364801 / 500000000) (-2070729599 / 1000000000) (Real.log (807 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (667625249 / 1000000000) ≤ -Real.log (500000 / 974801) ∧
    -Real.log (500000 / 974801) ≤ (2670501 / 4000000) := by
  have h := checkLog_sound (w := (474801 / 1474801)) (n := 12)
    (lo := (667625249 / 1000000000)) (hi := (2670501 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974801 / 500000) = 1/(500000 / 974801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (667625249 / 1000000000) (2670501 / 4000000) (Real.log (974801 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (974801 / 500000) = -Real.log (500000 / 974801) := by
    rw [show ((974801 / 500000) : ℝ) = ((500000 / 974801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (373475473 / 125000000) ≤ -Real.log (25199 / 500000) ∧
    -Real.log (25199 / 500000) ≤ (2987803789 / 1000000000) := by
  have h := checkLog_sound (w := (6051 / 56449)) (n := 12)
    (lo := (26901883 / 125000000)) (hi := (43043013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25199) = 1/(25199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2987803789 / 1000000000) (-373475473 / 125000000) (Real.log (25199 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133581361 / 200000000) ≤ -Real.log (1000000 / 1950151) ∧
    -Real.log (1000000 / 1950151) ≤ (333953403 / 500000000) := by
  have h := checkLog_sound (w := (950151 / 2950151)) (n := 12)
    (lo := (133581361 / 200000000)) (hi := (333953403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950151 / 1000000) = 1/(1000000 / 1950151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133581361 / 200000000) (333953403 / 500000000) (Real.log (1950151 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1950151 / 1000000) = -Real.log (1000000 / 1950151) := by
    rw [show ((1950151 / 1000000) : ℝ) = ((1000000 / 1950151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (74968921 / 25000000) ≤ -Real.log (49849 / 1000000) ∧
    -Real.log (49849 / 1000000) ≤ (599751369 / 200000000) := by
  have h := checkLog_sound (w := (12651 / 112349)) (n := 12)
    (lo := (5654203 / 25000000)) (hi := (226168121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49849) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49849) = 1/(49849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-599751369 / 200000000) (-74968921 / 25000000) (Real.log (49849 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (667207127 / 1000000000) ≤ -Real.log (1000000 / 1948787) ∧
    -Real.log (1000000 / 1948787) ≤ (83400891 / 125000000) := by
  have h := checkLog_sound (w := (948787 / 2948787)) (n := 12)
    (lo := (667207127 / 1000000000)) (hi := (83400891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948787 / 1000000) = 1/(1000000 / 1948787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (667207127 / 1000000000) (83400891 / 125000000) (Real.log (1948787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1948787 / 1000000) = -Real.log (1000000 / 1948787) := by
    rw [show ((1948787 / 1000000) : ℝ) = ((1000000 / 1948787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297176187 / 100000000) ≤ -Real.log (51213 / 1000000) ∧
    -Real.log (51213 / 1000000) ≤ (4754819 / 1600000) := by
  have h := checkLog_sound (w := (11287 / 113713)) (n := 12)
    (lo := (3983463 / 20000000)) (hi := (199173151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51213) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51213) = 1/(51213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4754819 / 1600000) (-297176187 / 100000000) (Real.log (51213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (667500087 / 1000000000) ≤ -Real.log (500000 / 974679) ∧
    -Real.log (500000 / 974679) ≤ (83437511 / 125000000) := by
  have h := checkLog_sound (w := (474679 / 1474679)) (n := 12)
    (lo := (667500087 / 1000000000)) (hi := (83437511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974679 / 500000) = 1/(500000 / 974679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (667500087 / 1000000000) (83437511 / 125000000) (Real.log (974679 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (974679 / 500000) = -Real.log (500000 / 974679) := by
    rw [show ((974679 / 500000) : ℝ) = ((500000 / 974679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (596594801 / 200000000) ≤ -Real.log (25321 / 500000) ∧
    -Real.log (25321 / 500000) ≤ (298297401 / 100000000) := by
  have h := checkLog_sound (w := (5929 / 56571)) (n := 12)
    (lo := (42077057 / 200000000)) (hi := (105192643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25321) = 1/(25321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-298297401 / 100000000) (-596594801 / 200000000) (Real.log (25321 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3655429033 / 1000000000) ≤ -Real.log (500000000000 / 19342057224493) ∧
    -Real.log (500000000000 / 19342057224493) ≤ (3655429039 / 1000000000) := by
  have h := checkLog_sound (w := (3342057224493 / 35342057224493)) (n := 12)
    (lo := (189693133 / 1000000000)) (hi := (94846567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19342057224493 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19342057224493 / 16000000000000) = 1/(500000000000 / 19342057224493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3655429033 / 1000000000) (3655429039 / 1000000000) (Real.log (19342057224493 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19342057224493 / 500000000000) = -Real.log (500000000000 / 19342057224493) := by
    rw [show ((19342057224493 / 500000000000) : ℝ) = ((500000000000 / 19342057224493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (733332729 / 200000000) ≤ -Real.log (500000000000 / 19560582960541) ∧
    -Real.log (500000000000 / 19560582960541) ≤ (3666663651 / 1000000000) := by
  have h := checkLog_sound (w := (3560582960541 / 35560582960541)) (n := 12)
    (lo := (40185549 / 200000000)) (hi := (100463873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19560582960541 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19560582960541 / 16000000000000) = 1/(500000000000 / 19560582960541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (733332729 / 200000000) (3666663651 / 1000000000) (Real.log (19560582960541 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (19560582960541 / 500000000000) = -Real.log (500000000000 / 19560582960541) := by
    rw [show ((19560582960541 / 500000000000) : ℝ) = ((500000000000 / 19560582960541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3638968997 / 1000000000) ≤ -Real.log (500000000000 / 19026292152383) ∧
    -Real.log (500000000000 / 19026292152383) ≤ (3638969003 / 1000000000) := by
  have h := checkLog_sound (w := (3026292152383 / 35026292152383)) (n := 12)
    (lo := (173233097 / 1000000000)) (hi := (86616549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19026292152383 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19026292152383 / 16000000000000) = 1/(500000000000 / 19026292152383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3638968997 / 1000000000) (3638969003 / 1000000000) (Real.log (19026292152383 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19026292152383 / 500000000000) = -Real.log (500000000000 / 19026292152383) := by
    rw [show ((19026292152383 / 500000000000) : ℝ) = ((500000000000 / 19026292152383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (912618523 / 250000000) ≤ -Real.log (125000000000 / 4811613877809) ∧
    -Real.log (125000000000 / 4811613877809) ≤ (1825237049 / 500000000) := by
  have h := checkLog_sound (w := (811613877809 / 8811613877809)) (n := 12)
    (lo := (11546137 / 62500000)) (hi := (184738193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4811613877809 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4811613877809 / 4000000000000) = 1/(125000000000 / 4811613877809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (912618523 / 250000000) (1825237049 / 500000000) (Real.log (4811613877809 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4811613877809 / 125000000000) = -Real.log (125000000000 / 4811613877809) := by
    rw [show ((4811613877809 / 125000000000) : ℝ) = ((125000000000 / 4811613877809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0132

end


