-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0192Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0192Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:17:58.377314+00:00
-- url     : https://prove2.me/theorems/850a8949-f59a-4283-b046-c4013528444b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0192Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0193Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0192Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0193Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0197Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0192Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0193Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0197Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0192Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0193Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0197Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0192Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0193Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0194Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0195Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0196Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0197Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0192Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0192
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

theorem reflection_log_1_neg : (5385031 / 20000000) ≤ -Real.log (2560 / 3351) ∧
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


theorem reflection_log_1 : Bounds (5385031 / 20000000) (269251551 / 1000000000) (Real.log (3351 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3351 / 2560) = -Real.log (2560 / 3351) := by
    rw [show ((3351 / 2560) : ℝ) = ((2560 / 3351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (369592843 / 1000000000) ≤ -Real.log (1769 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-92398211 / 250000000) (-369592843 / 1000000000) (Real.log (1769 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134401911 / 500000000) ≤ -Real.log (5120 / 6699) ∧
    -Real.log (5120 / 6699) ≤ (268803823 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 11819)) (n := 12)
    (lo := (134401911 / 500000000)) (hi := (268803823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6699 / 5120) = 1/(5120 / 6699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134401911 / 500000000) (268803823 / 1000000000) (Real.log (6699 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6699 / 5120) = -Real.log (5120 / 6699) := by
    rw [show ((6699 / 5120) : ℝ) = ((5120 / 6699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73749053 / 200000000) ≤ -Real.log (3541 / 5120) ∧
    -Real.log (3541 / 5120) ≤ (184372633 / 500000000) := by
  have h := checkLog_sound (w := (1579 / 8661)) (n := 12)
    (lo := (73749053 / 200000000)) (hi := (184372633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3541) = 1/(3541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-184372633 / 500000000) (-73749053 / 200000000) (Real.log (3541 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30073219 / 62500000) ≤ -Real.log (1280 / 2071) ∧
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


theorem reflection_log_5 : Bounds (30073219 / 62500000) (96234301 / 200000000) (Real.log (2071 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2071 / 1280) = -Real.log (1280 / 2071) := by
    rw [show ((2071 / 1280) : ℝ) = ((1280 / 2071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (481126433 / 500000000) ≤ -Real.log (489 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-240563217 / 250000000) (-481126433 / 500000000) (Real.log (489 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240223477 / 500000000) ≤ -Real.log (2560 / 4139) ∧
    -Real.log (2560 / 4139) ≤ (96089391 / 200000000) := by
  have h := checkLog_sound (w := (1579 / 6699)) (n := 12)
    (lo := (240223477 / 500000000)) (hi := (96089391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4139 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4139 / 2560) = 1/(2560 / 4139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240223477 / 500000000) (96089391 / 200000000) (Real.log (4139 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4139 / 2560) = -Real.log (2560 / 4139) := by
    rw [show ((4139 / 2560) : ℝ) = ((2560 / 4139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (959190077 / 1000000000) ≤ -Real.log (981 / 2560) ∧
    -Real.log (981 / 2560) ≤ (959190079 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2261)) (n := 12)
    (lo := (266042897 / 1000000000)) (hi := (133021449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 981) = 1/(981 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-959190079 / 1000000000) (-959190077 / 1000000000) (Real.log (981 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45965559 / 125000000) ≤ -Real.log (250000 / 361111) ∧
    -Real.log (250000 / 361111) ≤ (367724473 / 1000000000) := by
  have h := checkLog_sound (w := (111111 / 611111)) (n := 12)
    (lo := (45965559 / 125000000)) (hi := (367724473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361111 / 250000) = 1/(250000 / 361111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45965559 / 125000000) (367724473 / 1000000000) (Real.log (361111 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (361111 / 250000) = -Real.log (250000 / 361111) := by
    rw [show ((361111 / 250000) : ℝ) = ((250000 / 361111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73473233 / 125000000) ≤ -Real.log (138889 / 250000) ∧
    -Real.log (138889 / 250000) ≤ (117557173 / 200000000) := by
  have h := checkLog_sound (w := (111111 / 388889)) (n := 12)
    (lo := (73473233 / 125000000)) (hi := (117557173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 138889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 138889) = 1/(138889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-117557173 / 200000000) (-73473233 / 125000000) (Real.log (138889 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73667257 / 200000000) ≤ -Real.log (62500 / 90333) ∧
    -Real.log (62500 / 90333) ≤ (184168143 / 500000000) := by
  have h := checkLog_sound (w := (27833 / 152833)) (n := 12)
    (lo := (73667257 / 200000000)) (hi := (184168143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90333 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90333 / 62500) = 1/(62500 / 90333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73667257 / 200000000) (184168143 / 500000000) (Real.log (90333 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (90333 / 62500) = -Real.log (62500 / 90333) := by
    rw [show ((90333 / 62500) : ℝ) = ((62500 / 90333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58937833 / 100000000) ≤ -Real.log (34667 / 62500) ∧
    -Real.log (34667 / 62500) ≤ (589378331 / 1000000000) := by
  have h := checkLog_sound (w := (27833 / 97167)) (n := 12)
    (lo := (58937833 / 100000000)) (hi := (589378331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34667) = 1/(34667 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-589378331 / 1000000000) (-58937833 / 100000000) (Real.log (34667 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (286985579 / 1000000000) ≤ -Real.log (200000 / 266481) ∧
    -Real.log (200000 / 266481) ≤ (14349279 / 50000000) := by
  have h := checkLog_sound (w := (66481 / 466481)) (n := 12)
    (lo := (286985579 / 1000000000)) (hi := (14349279 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266481 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266481 / 200000) = 1/(200000 / 266481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (286985579 / 1000000000) (14349279 / 50000000) (Real.log (266481 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (266481 / 200000) = -Real.log (200000 / 266481) := by
    rw [show ((266481 / 200000) : ℝ) = ((200000 / 266481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50509197 / 125000000) ≤ -Real.log (133519 / 200000) ∧
    -Real.log (133519 / 200000) ≤ (404073577 / 1000000000) := by
  have h := checkLog_sound (w := (66481 / 333519)) (n := 12)
    (lo := (50509197 / 125000000)) (hi := (404073577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133519) = 1/(133519 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-404073577 / 1000000000) (-50509197 / 125000000) (Real.log (133519 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (143769281 / 500000000) ≤ -Real.log (500000 / 666571) ∧
    -Real.log (500000 / 666571) ≤ (287538563 / 1000000000) := by
  have h := checkLog_sound (w := (166571 / 1166571)) (n := 12)
    (lo := (143769281 / 500000000)) (hi := (287538563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666571 / 500000) = 1/(500000 / 666571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (143769281 / 500000000) (287538563 / 1000000000) (Real.log (666571 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (666571 / 500000) = -Real.log (500000 / 666571) := by
    rw [show ((666571 / 500000) : ℝ) = ((500000 / 666571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (405178149 / 1000000000) ≤ -Real.log (333429 / 500000) ∧
    -Real.log (333429 / 500000) ≤ (8103563 / 20000000) := by
  have h := checkLog_sound (w := (166571 / 833429)) (n := 12)
    (lo := (405178149 / 1000000000)) (hi := (8103563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333429) = 1/(333429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-8103563 / 20000000) (-405178149 / 1000000000) (Real.log (333429 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (14929849 / 15625000) ≤ -Real.log (500000000000 / 1299998560001) ∧
    -Real.log (500000000000 / 1299998560001) ≤ (477755169 / 500000000) := by
  have h := checkLog_sound (w := (299998560001 / 2299998560001)) (n := 12)
    (lo := (65590789 / 250000000)) (hi := (262363157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299998560001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1299998560001 / 1000000000000) = 1/(500000000000 / 1299998560001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14929849 / 15625000) (477755169 / 500000000) (Real.log (1299998560001 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1299998560001 / 500000000000) = -Real.log (500000000000 / 1299998560001) := by
    rw [show ((1299998560001 / 500000000000) : ℝ) = ((500000000000 / 1299998560001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (191542923 / 200000000) ≤ -Real.log (500000000000 / 1302867280123) ∧
    -Real.log (500000000000 / 1302867280123) ≤ (957714617 / 1000000000) := by
  have h := checkLog_sound (w := (302867280123 / 2302867280123)) (n := 12)
    (lo := (52913487 / 200000000)) (hi := (66141859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302867280123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1302867280123 / 1000000000000) = 1/(500000000000 / 1302867280123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (191542923 / 200000000) (957714617 / 1000000000) (Real.log (1302867280123 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1302867280123 / 500000000000) = -Real.log (500000000000 / 1302867280123) := by
    rw [show ((1302867280123 / 500000000000) : ℝ) = ((500000000000 / 1302867280123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (172764789 / 250000000) ≤ -Real.log (500000000000 / 997914154539) ∧
    -Real.log (500000000000 / 997914154539) ≤ (691059157 / 1000000000) := by
  have h := checkLog_sound (w := (497914154539 / 1497914154539)) (n := 12)
    (lo := (172764789 / 250000000)) (hi := (691059157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997914154539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997914154539 / 500000000000) = 1/(500000000000 / 997914154539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (172764789 / 250000000) (691059157 / 1000000000) (Real.log (997914154539 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (997914154539 / 500000000000) = -Real.log (500000000000 / 997914154539) := by
    rw [show ((997914154539 / 500000000000) : ℝ) = ((500000000000 / 997914154539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (692716711 / 1000000000) ≤ -Real.log (500000000000 / 999569623519) ∧
    -Real.log (500000000000 / 999569623519) ≤ (86589589 / 125000000) := by
  have h := checkLog_sound (w := (499569623519 / 1499569623519)) (n := 12)
    (lo := (692716711 / 1000000000)) (hi := (86589589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999569623519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999569623519 / 500000000000) = 1/(500000000000 / 999569623519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (692716711 / 1000000000) (86589589 / 125000000) (Real.log (999569623519 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (999569623519 / 500000000000) = -Real.log (500000000000 / 999569623519) := by
    rw [show ((999569623519 / 500000000000) : ℝ) = ((500000000000 / 999569623519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0192

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0193Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0193
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

theorem reflection_log_1_neg : (134401911 / 500000000) ≤ -Real.log (5120 / 6699) ∧
    -Real.log (5120 / 6699) ≤ (268803823 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 11819)) (n := 12)
    (lo := (134401911 / 500000000)) (hi := (268803823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6699 / 5120) = 1/(5120 / 6699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134401911 / 500000000) (268803823 / 1000000000) (Real.log (6699 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6699 / 5120) = -Real.log (5120 / 6699) := by
    rw [show ((6699 / 5120) : ℝ) = ((5120 / 6699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73749053 / 200000000) ≤ -Real.log (3541 / 5120) ∧
    -Real.log (3541 / 5120) ≤ (184372633 / 500000000) := by
  have h := checkLog_sound (w := (1579 / 8661)) (n := 12)
    (lo := (73749053 / 200000000)) (hi := (184372633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3541) = 1/(3541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-184372633 / 500000000) (-73749053 / 200000000) (Real.log (3541 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134177947 / 500000000) ≤ -Real.log (640 / 837) ∧
    -Real.log (640 / 837) ≤ (53671179 / 200000000) := by
  have h := checkLog_sound (w := (197 / 1477)) (n := 12)
    (lo := (134177947 / 500000000)) (hi := (53671179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 640) = 1/(640 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134177947 / 500000000) (53671179 / 200000000) (Real.log (837 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (837 / 640) = -Real.log (640 / 837) := by
    rw [show ((837 / 640) : ℝ) = ((640 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (183949203 / 500000000) ≤ -Real.log (443 / 640) ∧
    -Real.log (443 / 640) ≤ (367898407 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1083)) (n := 12)
    (lo := (183949203 / 500000000)) (hi := (367898407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 443) = 1/(443 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-367898407 / 1000000000) (-183949203 / 500000000) (Real.log (443 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240223477 / 500000000) ≤ -Real.log (2560 / 4139) ∧
    -Real.log (2560 / 4139) ≤ (96089391 / 200000000) := by
  have h := checkLog_sound (w := (1579 / 6699)) (n := 12)
    (lo := (240223477 / 500000000)) (hi := (96089391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4139 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4139 / 2560) = 1/(2560 / 4139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240223477 / 500000000) (96089391 / 200000000) (Real.log (4139 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4139 / 2560) = -Real.log (2560 / 4139) := by
    rw [show ((4139 / 2560) : ℝ) = ((2560 / 4139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (959190077 / 1000000000) ≤ -Real.log (981 / 2560) ∧
    -Real.log (981 / 2560) ≤ (959190079 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2261)) (n := 12)
    (lo := (266042897 / 1000000000)) (hi := (133021449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 981) = 1/(981 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-959190079 / 1000000000) (-959190077 / 1000000000) (Real.log (981 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36711367 / 100000000) ≤ -Real.log (500000 / 721781) ∧
    -Real.log (500000 / 721781) ≤ (367113671 / 1000000000) := by
  have h := checkLog_sound (w := (221781 / 1221781)) (n := 12)
    (lo := (36711367 / 100000000)) (hi := (367113671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721781 / 500000) = 1/(500000 / 721781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36711367 / 100000000) (367113671 / 1000000000) (Real.log (721781 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (721781 / 500000) = -Real.log (500000 / 721781) := by
    rw [show ((721781 / 500000) : ℝ) = ((500000 / 721781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23447981 / 40000000) ≤ -Real.log (278219 / 500000) ∧
    -Real.log (278219 / 500000) ≤ (293099763 / 500000000) := by
  have h := checkLog_sound (w := (221781 / 778219)) (n := 12)
    (lo := (23447981 / 40000000)) (hi := (293099763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 278219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 278219) = 1/(278219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-293099763 / 500000000) (-23447981 / 40000000) (Real.log (278219 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91931291 / 250000000) ≤ -Real.log (200000 / 288889) ∧
    -Real.log (200000 / 288889) ≤ (73545033 / 200000000) := by
  have h := checkLog_sound (w := (88889 / 488889)) (n := 12)
    (lo := (91931291 / 250000000)) (hi := (73545033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288889 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288889 / 200000) = 1/(200000 / 288889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91931291 / 250000000) (73545033 / 200000000) (Real.log (288889 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288889 / 200000) = -Real.log (200000 / 288889) := by
    rw [show ((288889 / 200000) : ℝ) = ((200000 / 288889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36736729 / 62500000) ≤ -Real.log (111111 / 200000) ∧
    -Real.log (111111 / 200000) ≤ (117557533 / 200000000) := by
  have h := checkLog_sound (w := (88889 / 311111)) (n := 12)
    (lo := (36736729 / 62500000)) (hi := (117557533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111111) = 1/(111111 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-117557533 / 200000000) (-36736729 / 62500000) (Real.log (111111 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (143216521 / 500000000) ≤ -Real.log (1000000 / 1331669) ∧
    -Real.log (1000000 / 1331669) ≤ (286433043 / 1000000000) := by
  have h := checkLog_sound (w := (331669 / 2331669)) (n := 12)
    (lo := (143216521 / 500000000)) (hi := (286433043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331669 / 1000000) = 1/(1000000 / 1331669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (143216521 / 500000000) (286433043 / 1000000000) (Real.log (1331669 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1331669 / 1000000) = -Real.log (1000000 / 1331669) := by
    rw [show ((1331669 / 1000000) : ℝ) = ((1000000 / 1331669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (402971719 / 1000000000) ≤ -Real.log (668331 / 1000000) ∧
    -Real.log (668331 / 1000000) ≤ (10074293 / 25000000) := by
  have h := checkLog_sound (w := (331669 / 1668331)) (n := 12)
    (lo := (402971719 / 1000000000)) (hi := (10074293 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668331) = 1/(668331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10074293 / 25000000) (-402971719 / 1000000000) (Real.log (668331 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28698633 / 100000000) ≤ -Real.log (500000 / 666203) ∧
    -Real.log (500000 / 666203) ≤ (286986331 / 1000000000) := by
  have h := checkLog_sound (w := (166203 / 1166203)) (n := 12)
    (lo := (28698633 / 100000000)) (hi := (286986331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666203 / 500000) = 1/(500000 / 666203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28698633 / 100000000) (286986331 / 1000000000) (Real.log (666203 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (666203 / 500000) = -Real.log (500000 / 666203) := by
    rw [show ((666203 / 500000) : ℝ) = ((500000 / 666203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (202037537 / 500000000) ≤ -Real.log (333797 / 500000) ∧
    -Real.log (333797 / 500000) ≤ (16163003 / 40000000) := by
  have h := checkLog_sound (w := (166203 / 833797)) (n := 12)
    (lo := (202037537 / 500000000)) (hi := (16163003 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333797) = 1/(333797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16163003 / 40000000) (-202037537 / 500000000) (Real.log (333797 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (476656597 / 500000000) ≤ -Real.log (31250000000 / 81071588389) ∧
    -Real.log (31250000000 / 81071588389) ≤ (238328299 / 250000000) := by
  have h := checkLog_sound (w := (18571588389 / 143571588389)) (n := 12)
    (lo := (130083007 / 500000000)) (hi := (52033203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81071588389 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(81071588389 / 62500000000) = 1/(31250000000 / 81071588389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (476656597 / 500000000) (238328299 / 250000000) (Real.log (81071588389 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (81071588389 / 31250000000) = -Real.log (31250000000 / 81071588389) := by
    rw [show ((81071588389 / 31250000000) : ℝ) = ((31250000000 / 81071588389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (955512829 / 1000000000) ≤ -Real.log (250000000000 / 650000900001) ∧
    -Real.log (250000000000 / 650000900001) ≤ (955512831 / 1000000000) := by
  have h := checkLog_sound (w := (150000900001 / 1150000900001)) (n := 12)
    (lo := (262365649 / 1000000000)) (hi := (5247313 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650000900001 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(650000900001 / 500000000000) = 1/(250000000000 / 650000900001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (955512829 / 1000000000) (955512831 / 1000000000) (Real.log (650000900001 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (650000900001 / 250000000000) = -Real.log (250000000000 / 650000900001) := by
    rw [show ((650000900001 / 250000000000) : ℝ) = ((250000000000 / 650000900001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (689404761 / 1000000000) ≤ -Real.log (500000000000 / 996264575487) ∧
    -Real.log (500000000000 / 996264575487) ≤ (344702381 / 500000000) := by
  have h := checkLog_sound (w := (496264575487 / 1496264575487)) (n := 12)
    (lo := (689404761 / 1000000000)) (hi := (344702381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996264575487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996264575487 / 500000000000) = 1/(500000000000 / 996264575487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (689404761 / 1000000000) (344702381 / 500000000) (Real.log (996264575487 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (996264575487 / 500000000000) = -Real.log (500000000000 / 996264575487) := by
    rw [show ((996264575487 / 500000000000) : ℝ) = ((500000000000 / 996264575487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (138212281 / 200000000) ≤ -Real.log (50000000000 / 99791639829) ∧
    -Real.log (50000000000 / 99791639829) ≤ (345530703 / 500000000) := by
  have h := checkLog_sound (w := (49791639829 / 149791639829)) (n := 12)
    (lo := (138212281 / 200000000)) (hi := (345530703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99791639829 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99791639829 / 50000000000) = 1/(50000000000 / 99791639829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (138212281 / 200000000) (345530703 / 500000000) (Real.log (99791639829 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (99791639829 / 50000000000) = -Real.log (50000000000 / 99791639829) := by
    rw [show ((99791639829 / 50000000000) : ℝ) = ((50000000000 / 99791639829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0193

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0194Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0194
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

theorem reflection_log_1_neg : (134177947 / 500000000) ≤ -Real.log (640 / 837) ∧
    -Real.log (640 / 837) ≤ (53671179 / 200000000) := by
  have h := checkLog_sound (w := (197 / 1477)) (n := 12)
    (lo := (134177947 / 500000000)) (hi := (53671179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 640) = 1/(640 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134177947 / 500000000) (53671179 / 200000000) (Real.log (837 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (837 / 640) = -Real.log (640 / 837) := by
    rw [show ((837 / 640) : ℝ) = ((640 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (183949203 / 500000000) ≤ -Real.log (443 / 640) ∧
    -Real.log (443 / 640) ≤ (367898407 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1083)) (n := 12)
    (lo := (183949203 / 500000000)) (hi := (367898407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 443) = 1/(443 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-367898407 / 1000000000) (-183949203 / 500000000) (Real.log (443 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53581553 / 200000000) ≤ -Real.log (5120 / 6693) ∧
    -Real.log (5120 / 6693) ≤ (133953883 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 11813)) (n := 12)
    (lo := (53581553 / 200000000)) (hi := (133953883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6693 / 5120) = 1/(5120 / 6693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53581553 / 200000000) (133953883 / 500000000) (Real.log (6693 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6693 / 5120) = -Real.log (5120 / 6693) := by
    rw [show ((6693 / 5120) : ℝ) = ((5120 / 6693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (367052263 / 1000000000) ≤ -Real.log (3547 / 5120) ∧
    -Real.log (3547 / 5120) ≤ (45881533 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 8667)) (n := 12)
    (lo := (367052263 / 1000000000)) (hi := (45881533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3547) = 1/(3547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45881533 / 125000000) (-367052263 / 1000000000) (Real.log (3547 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (478996277 / 1000000000) ≤ -Real.log (2560 / 4133) ∧
    -Real.log (2560 / 4133) ≤ (239498139 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 6693)) (n := 12)
    (lo := (478996277 / 1000000000)) (hi := (239498139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4133 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4133 / 2560) = 1/(2560 / 4133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (478996277 / 1000000000) (239498139 / 500000000) (Real.log (4133 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4133 / 2560) = -Real.log (2560 / 4133) := by
    rw [show ((4133 / 2560) : ℝ) = ((2560 / 4133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (953092497 / 1000000000) ≤ -Real.log (987 / 2560) ∧
    -Real.log (987 / 2560) ≤ (953092499 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2267)) (n := 12)
    (lo := (259945317 / 1000000000)) (hi := (129972659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 987) = 1/(987 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-953092499 / 1000000000) (-953092497 / 1000000000) (Real.log (987 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (366501801 / 1000000000) ≤ -Real.log (1000000 / 1442679) ∧
    -Real.log (1000000 / 1442679) ≤ (183250901 / 500000000) := by
  have h := checkLog_sound (w := (442679 / 2442679)) (n := 12)
    (lo := (366501801 / 1000000000)) (hi := (183250901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1442679 / 1000000) = 1/(1000000 / 1442679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (366501801 / 1000000000) (183250901 / 500000000) (Real.log (1442679 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1442679 / 1000000) = -Real.log (1000000 / 1442679) := by
    rw [show ((1442679 / 1000000) : ℝ) = ((1000000 / 1442679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (584613903 / 1000000000) ≤ -Real.log (557321 / 1000000) ∧
    -Real.log (557321 / 1000000) ≤ (36538369 / 62500000) := by
  have h := checkLog_sound (w := (442679 / 1557321)) (n := 12)
    (lo := (584613903 / 1000000000)) (hi := (36538369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 557321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 557321) = 1/(557321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36538369 / 62500000) (-584613903 / 1000000000) (Real.log (557321 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (367114363 / 1000000000) ≤ -Real.log (1000000 / 1443563) ∧
    -Real.log (1000000 / 1443563) ≤ (91778591 / 250000000) := by
  have h := checkLog_sound (w := (443563 / 2443563)) (n := 12)
    (lo := (367114363 / 1000000000)) (hi := (91778591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443563 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443563 / 1000000) = 1/(1000000 / 1443563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (367114363 / 1000000000) (91778591 / 250000000) (Real.log (1443563 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1443563 / 1000000) = -Real.log (1000000 / 1443563) := by
    rw [show ((1443563 / 1000000) : ℝ) = ((1000000 / 1443563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (293100661 / 500000000) ≤ -Real.log (556437 / 1000000) ∧
    -Real.log (556437 / 1000000) ≤ (586201323 / 1000000000) := by
  have h := checkLog_sound (w := (443563 / 1556437)) (n := 12)
    (lo := (293100661 / 500000000)) (hi := (586201323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 556437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 556437) = 1/(556437 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-586201323 / 1000000000) (-293100661 / 500000000) (Real.log (556437 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (285880951 / 1000000000) ≤ -Real.log (500000 / 665467) ∧
    -Real.log (500000 / 665467) ≤ (35735119 / 125000000) := by
  have h := checkLog_sound (w := (165467 / 1165467)) (n := 12)
    (lo := (285880951 / 1000000000)) (hi := (35735119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665467 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665467 / 500000) = 1/(500000 / 665467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (285880951 / 1000000000) (35735119 / 125000000) (Real.log (665467 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (665467 / 500000) = -Real.log (500000 / 665467) := by
    rw [show ((665467 / 500000) : ℝ) = ((500000 / 665467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (401872569 / 1000000000) ≤ -Real.log (334533 / 500000) ∧
    -Real.log (334533 / 500000) ≤ (40187257 / 100000000) := by
  have h := checkLog_sound (w := (165467 / 834533)) (n := 12)
    (lo := (401872569 / 1000000000)) (hi := (40187257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334533) = 1/(334533 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40187257 / 100000000) (-401872569 / 1000000000) (Real.log (334533 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (286433793 / 1000000000) ≤ -Real.log (100000 / 133167) ∧
    -Real.log (100000 / 133167) ≤ (143216897 / 500000000) := by
  have h := checkLog_sound (w := (33167 / 233167)) (n := 12)
    (lo := (286433793 / 1000000000)) (hi := (143216897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133167 / 100000) = 1/(100000 / 133167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286433793 / 1000000000) (143216897 / 500000000) (Real.log (133167 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (133167 / 100000) = -Real.log (100000 / 133167) := by
    rw [show ((133167 / 100000) : ℝ) = ((100000 / 133167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (80594643 / 200000000) ≤ -Real.log (66833 / 100000) ∧
    -Real.log (66833 / 100000) ≤ (12592913 / 31250000) := by
  have h := checkLog_sound (w := (33167 / 166833)) (n := 12)
    (lo := (80594643 / 200000000)) (hi := (12592913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66833) = 1/(66833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-12592913 / 31250000) (-80594643 / 200000000) (Real.log (66833 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118889463 / 125000000) ≤ -Real.log (250000000000 / 647149039781) ∧
    -Real.log (250000000000 / 647149039781) ≤ (475557853 / 500000000) := by
  have h := checkLog_sound (w := (147149039781 / 1147149039781)) (n := 12)
    (lo := (64492131 / 250000000)) (hi := (10318741 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647149039781 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(647149039781 / 500000000000) = 1/(250000000000 / 647149039781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118889463 / 125000000) (475557853 / 500000000) (Real.log (647149039781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (647149039781 / 250000000000) = -Real.log (250000000000 / 647149039781) := by
    rw [show ((647149039781 / 250000000000) : ℝ) = ((250000000000 / 647149039781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (238328921 / 250000000) ≤ -Real.log (250000000000 / 648574321981) ∧
    -Real.log (250000000000 / 648574321981) ≤ (476657843 / 500000000) := by
  have h := checkLog_sound (w := (148574321981 / 1148574321981)) (n := 12)
    (lo := (32521063 / 125000000)) (hi := (52033701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648574321981 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(648574321981 / 500000000000) = 1/(250000000000 / 648574321981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (238328921 / 250000000) (476657843 / 500000000) (Real.log (648574321981 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (648574321981 / 250000000000) = -Real.log (250000000000 / 648574321981) := by
    rw [show ((648574321981 / 250000000000) : ℝ) = ((250000000000 / 648574321981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8596919 / 12500000) ≤ -Real.log (250000000000 / 497310429763) ∧
    -Real.log (250000000000 / 497310429763) ≤ (687753521 / 1000000000) := by
  have h := checkLog_sound (w := (247310429763 / 747310429763)) (n := 12)
    (lo := (8596919 / 12500000)) (hi := (687753521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497310429763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497310429763 / 250000000000) = 1/(250000000000 / 497310429763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (8596919 / 12500000) (687753521 / 1000000000) (Real.log (497310429763 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (497310429763 / 250000000000) = -Real.log (250000000000 / 497310429763) := by
    rw [show ((497310429763 / 250000000000) : ℝ) = ((250000000000 / 497310429763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (689407009 / 1000000000) ≤ -Real.log (500000000000 / 996266814299) ∧
    -Real.log (500000000000 / 996266814299) ≤ (68940701 / 100000000) := by
  have h := checkLog_sound (w := (496266814299 / 1496266814299)) (n := 12)
    (lo := (689407009 / 1000000000)) (hi := (68940701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996266814299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996266814299 / 500000000000) = 1/(500000000000 / 996266814299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (689407009 / 1000000000) (68940701 / 100000000) (Real.log (996266814299 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (996266814299 / 500000000000) = -Real.log (500000000000 / 996266814299) := by
    rw [show ((996266814299 / 500000000000) : ℝ) = ((500000000000 / 996266814299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0194

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0195Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0195
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

theorem reflection_log_1_neg : (53581553 / 200000000) ≤ -Real.log (5120 / 6693) ∧
    -Real.log (5120 / 6693) ≤ (133953883 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 11813)) (n := 12)
    (lo := (53581553 / 200000000)) (hi := (133953883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6693 / 5120) = 1/(5120 / 6693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53581553 / 200000000) (133953883 / 500000000) (Real.log (6693 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6693 / 5120) = -Real.log (5120 / 6693) := by
    rw [show ((6693 / 5120) : ℝ) = ((5120 / 6693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (367052263 / 1000000000) ≤ -Real.log (3547 / 5120) ∧
    -Real.log (3547 / 5120) ≤ (45881533 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 8667)) (n := 12)
    (lo := (367052263 / 1000000000)) (hi := (45881533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3547) = 1/(3547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45881533 / 125000000) (-367052263 / 1000000000) (Real.log (3547 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53491887 / 200000000) ≤ -Real.log (512 / 669) ∧
    -Real.log (512 / 669) ≤ (66864859 / 250000000) := by
  have h := checkLog_sound (w := (157 / 1181)) (n := 12)
    (lo := (53491887 / 200000000)) (hi := (66864859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669 / 512) = 1/(512 / 669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53491887 / 200000000) (66864859 / 250000000) (Real.log (669 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (669 / 512) = -Real.log (512 / 669) := by
    rw [show ((669 / 512) : ℝ) = ((512 / 669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73241367 / 200000000) ≤ -Real.log (355 / 512) ∧
    -Real.log (355 / 512) ≤ (91551709 / 250000000) := by
  have h := checkLog_sound (w := (157 / 867)) (n := 12)
    (lo := (73241367 / 200000000)) (hi := (91551709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 355) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 355) = 1/(355 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91551709 / 250000000) (-73241367 / 200000000) (Real.log (355 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (478996277 / 1000000000) ≤ -Real.log (2560 / 4133) ∧
    -Real.log (2560 / 4133) ≤ (239498139 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 6693)) (n := 12)
    (lo := (478996277 / 1000000000)) (hi := (239498139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4133 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4133 / 2560) = 1/(2560 / 4133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (478996277 / 1000000000) (239498139 / 500000000) (Real.log (4133 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4133 / 2560) = -Real.log (2560 / 4133) := by
    rw [show ((4133 / 2560) : ℝ) = ((2560 / 4133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (953092497 / 1000000000) ≤ -Real.log (987 / 2560) ∧
    -Real.log (987 / 2560) ≤ (953092499 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2267)) (n := 12)
    (lo := (259945317 / 1000000000)) (hi := (129972659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 987) = 1/(987 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-953092499 / 1000000000) (-953092497 / 1000000000) (Real.log (987 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119567537 / 250000000) ≤ -Real.log (256 / 413) ∧
    -Real.log (256 / 413) ≤ (478270149 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 669)) (n := 12)
    (lo := (119567537 / 250000000)) (hi := (478270149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413 / 256) = 1/(256 / 413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119567537 / 250000000) (478270149 / 1000000000) (Real.log (413 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (413 / 256) = -Real.log (256 / 413) := by
    rw [show ((413 / 256) : ℝ) = ((256 / 413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (950057593 / 1000000000) ≤ -Real.log (99 / 256) ∧
    -Real.log (99 / 256) ≤ (190011519 / 200000000) := by
  have h := checkLog_sound (w := (29 / 227)) (n := 12)
    (lo := (256910413 / 1000000000)) (hi := (128455207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 99) = 1/(99 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190011519 / 200000000) (-950057593 / 1000000000) (Real.log (99 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91472563 / 250000000) ≤ -Real.log (1000000 / 1441797) ∧
    -Real.log (1000000 / 1441797) ≤ (365890253 / 1000000000) := by
  have h := checkLog_sound (w := (441797 / 2441797)) (n := 12)
    (lo := (91472563 / 250000000)) (hi := (365890253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441797 / 1000000) = 1/(1000000 / 1441797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91472563 / 250000000) (365890253 / 1000000000) (Real.log (1441797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1441797 / 1000000) = -Real.log (1000000 / 1441797) := by
    rw [show ((1441797 / 1000000) : ℝ) = ((1000000 / 1441797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (583032583 / 1000000000) ≤ -Real.log (558203 / 1000000) ∧
    -Real.log (558203 / 1000000) ≤ (72879073 / 125000000) := by
  have h := checkLog_sound (w := (441797 / 1558203)) (n := 12)
    (lo := (583032583 / 1000000000)) (hi := (72879073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 558203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 558203) = 1/(558203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72879073 / 125000000) (-583032583 / 1000000000) (Real.log (558203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183251247 / 500000000) ≤ -Real.log (25000 / 36067) ∧
    -Real.log (25000 / 36067) ≤ (73300499 / 200000000) := by
  have h := checkLog_sound (w := (11067 / 61067)) (n := 12)
    (lo := (183251247 / 500000000)) (hi := (73300499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36067 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36067 / 25000) = 1/(25000 / 36067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183251247 / 500000000) (73300499 / 200000000) (Real.log (36067 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (36067 / 25000) = -Real.log (25000 / 36067) := by
    rw [show ((36067 / 25000) : ℝ) = ((25000 / 36067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (584615697 / 1000000000) ≤ -Real.log (13933 / 25000) ∧
    -Real.log (13933 / 25000) ≤ (292307849 / 500000000) := by
  have h := checkLog_sound (w := (11067 / 38933)) (n := 12)
    (lo := (584615697 / 1000000000)) (hi := (292307849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13933) = 1/(13933 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-292307849 / 500000000) (-584615697 / 1000000000) (Real.log (13933 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (142664653 / 500000000) ≤ -Real.log (5000 / 6651) ∧
    -Real.log (5000 / 6651) ≤ (285329307 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 11651)) (n := 12)
    (lo := (142664653 / 500000000)) (hi := (285329307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5000) = 1/(5000 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (142664653 / 500000000) (285329307 / 1000000000) (Real.log (6651 / 5000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (6651 / 5000) = -Real.log (5000 / 6651) := by
    rw [show ((6651 / 5000) : ℝ) = ((5000 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (200388059 / 500000000) ≤ -Real.log (3349 / 5000) ∧
    -Real.log (3349 / 5000) ≤ (400776119 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 8349)) (n := 12)
    (lo := (200388059 / 500000000)) (hi := (400776119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3349) = 1/(3349 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-400776119 / 1000000000) (-200388059 / 500000000) (Real.log (3349 / 5000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (142940851 / 500000000) ≤ -Real.log (200000 / 266187) ∧
    -Real.log (200000 / 266187) ≤ (285881703 / 1000000000) := by
  have h := checkLog_sound (w := (66187 / 466187)) (n := 12)
    (lo := (142940851 / 500000000)) (hi := (285881703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266187 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266187 / 200000) = 1/(200000 / 266187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142940851 / 500000000) (285881703 / 1000000000) (Real.log (266187 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (266187 / 200000) = -Real.log (200000 / 266187) := by
    rw [show ((266187 / 200000) : ℝ) = ((200000 / 266187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (401874063 / 1000000000) ≤ -Real.log (133813 / 200000) ∧
    -Real.log (133813 / 200000) ≤ (25117129 / 62500000) := by
  have h := checkLog_sound (w := (66187 / 333813)) (n := 12)
    (lo := (401874063 / 1000000000)) (hi := (25117129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133813) = 1/(133813 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-25117129 / 62500000) (-401874063 / 1000000000) (Real.log (133813 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189784567 / 200000000) ≤ -Real.log (250000000000 / 645731481199) ∧
    -Real.log (250000000000 / 645731481199) ≤ (948922837 / 1000000000) := by
  have h := checkLog_sound (w := (145731481199 / 1145731481199)) (n := 12)
    (lo := (51155131 / 200000000)) (hi := (31971957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645731481199 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(645731481199 / 500000000000) = 1/(250000000000 / 645731481199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189784567 / 200000000) (948922837 / 1000000000) (Real.log (645731481199 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645731481199 / 250000000000) = -Real.log (250000000000 / 645731481199) := by
    rw [show ((645731481199 / 250000000000) : ℝ) = ((250000000000 / 645731481199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59444887 / 62500000) ≤ -Real.log (20000000000 / 51772051963) ∧
    -Real.log (20000000000 / 51772051963) ≤ (475559097 / 500000000) := by
  have h := checkLog_sound (w := (11772051963 / 91772051963)) (n := 12)
    (lo := (64492753 / 250000000)) (hi := (257971013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51772051963 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51772051963 / 40000000000) = 1/(20000000000 / 51772051963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59444887 / 62500000) (475559097 / 500000000) (Real.log (51772051963 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51772051963 / 20000000000) = -Real.log (20000000000 / 51772051963) := by
    rw [show ((51772051963 / 20000000000) : ℝ) = ((20000000000 / 51772051963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27444217 / 40000000) ≤ -Real.log (250000000000 / 496491489997) ∧
    -Real.log (250000000000 / 496491489997) ≤ (343052713 / 500000000) := by
  have h := checkLog_sound (w := (246491489997 / 746491489997)) (n := 12)
    (lo := (27444217 / 40000000)) (hi := (343052713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496491489997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496491489997 / 250000000000) = 1/(250000000000 / 496491489997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (27444217 / 40000000) (343052713 / 500000000) (Real.log (496491489997 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (496491489997 / 250000000000) = -Real.log (250000000000 / 496491489997) := by
    rw [show ((496491489997 / 250000000000) : ℝ) = ((250000000000 / 496491489997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (343877883 / 500000000) ≤ -Real.log (250000000000 / 497311546711) ∧
    -Real.log (250000000000 / 497311546711) ≤ (687755767 / 1000000000) := by
  have h := checkLog_sound (w := (247311546711 / 747311546711)) (n := 12)
    (lo := (343877883 / 500000000)) (hi := (687755767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497311546711 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497311546711 / 250000000000) = 1/(250000000000 / 497311546711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (343877883 / 500000000) (687755767 / 1000000000) (Real.log (497311546711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (497311546711 / 250000000000) = -Real.log (250000000000 / 497311546711) := by
    rw [show ((497311546711 / 250000000000) : ℝ) = ((250000000000 / 497311546711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0195

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0196Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0196
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

theorem reflection_log_1_neg : (53491887 / 200000000) ≤ -Real.log (512 / 669) ∧
    -Real.log (512 / 669) ≤ (66864859 / 250000000) := by
  have h := checkLog_sound (w := (157 / 1181)) (n := 12)
    (lo := (53491887 / 200000000)) (hi := (66864859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669 / 512) = 1/(512 / 669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53491887 / 200000000) (66864859 / 250000000) (Real.log (669 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (669 / 512) = -Real.log (512 / 669) := by
    rw [show ((669 / 512) : ℝ) = ((512 / 669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73241367 / 200000000) ≤ -Real.log (355 / 512) ∧
    -Real.log (355 / 512) ≤ (91551709 / 250000000) := by
  have h := checkLog_sound (w := (157 / 867)) (n := 12)
    (lo := (73241367 / 200000000)) (hi := (91551709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 355) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 355) = 1/(355 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91551709 / 250000000) (-73241367 / 200000000) (Real.log (355 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33376363 / 125000000) ≤ -Real.log (5120 / 6687) ∧
    -Real.log (5120 / 6687) ≤ (53402181 / 200000000) := by
  have h := checkLog_sound (w := (1567 / 11807)) (n := 12)
    (lo := (33376363 / 125000000)) (hi := (53402181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6687 / 5120) = 1/(5120 / 6687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33376363 / 125000000) (53402181 / 200000000) (Real.log (6687 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6687 / 5120) = -Real.log (5120 / 6687) := by
    rw [show ((6687 / 5120) : ℝ) = ((5120 / 6687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (182681061 / 500000000) ≤ -Real.log (3553 / 5120) ∧
    -Real.log (3553 / 5120) ≤ (365362123 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 8673)) (n := 12)
    (lo := (182681061 / 500000000)) (hi := (365362123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3553) = 1/(3553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-365362123 / 1000000000) (-182681061 / 500000000) (Real.log (3553 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119567537 / 250000000) ≤ -Real.log (256 / 413) ∧
    -Real.log (256 / 413) ≤ (478270149 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 669)) (n := 12)
    (lo := (119567537 / 250000000)) (hi := (478270149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413 / 256) = 1/(256 / 413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119567537 / 250000000) (478270149 / 1000000000) (Real.log (413 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (413 / 256) = -Real.log (256 / 413) := by
    rw [show ((413 / 256) : ℝ) = ((256 / 413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (950057593 / 1000000000) ≤ -Real.log (99 / 256) ∧
    -Real.log (99 / 256) ≤ (190011519 / 200000000) := by
  have h := checkLog_sound (w := (29 / 227)) (n := 12)
    (lo := (256910413 / 1000000000)) (hi := (128455207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 99) = 1/(99 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190011519 / 200000000) (-950057593 / 1000000000) (Real.log (99 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119385873 / 250000000) ≤ -Real.log (2560 / 4127) ∧
    -Real.log (2560 / 4127) ≤ (477543493 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 6687)) (n := 12)
    (lo := (119385873 / 250000000)) (hi := (477543493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4127 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4127 / 2560) = 1/(2560 / 4127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119385873 / 250000000) (477543493 / 1000000000) (Real.log (4127 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4127 / 2560) = -Real.log (2560 / 4127) := by
    rw [show ((4127 / 2560) : ℝ) = ((2560 / 4127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14797373 / 15625000) ≤ -Real.log (993 / 2560) ∧
    -Real.log (993 / 2560) ≤ (473515937 / 500000000) := by
  have h := checkLog_sound (w := (287 / 2273)) (n := 12)
    (lo := (63471173 / 250000000)) (hi := (253884693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 993) = 1/(993 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-473515937 / 500000000) (-14797373 / 15625000) (Real.log (993 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45659791 / 125000000) ≤ -Real.log (200000 / 288183) ∧
    -Real.log (200000 / 288183) ≤ (365278329 / 1000000000) := by
  have h := checkLog_sound (w := (88183 / 488183)) (n := 12)
    (lo := (45659791 / 125000000)) (hi := (365278329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288183 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288183 / 200000) = 1/(200000 / 288183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45659791 / 125000000) (365278329 / 1000000000) (Real.log (288183 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (288183 / 200000) = -Real.log (200000 / 288183) := by
    rw [show ((288183 / 200000) : ℝ) = ((200000 / 288183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1817043 / 3125000) ≤ -Real.log (111817 / 200000) ∧
    -Real.log (111817 / 200000) ≤ (581453761 / 1000000000) := by
  have h := checkLog_sound (w := (88183 / 311817)) (n := 12)
    (lo := (1817043 / 3125000)) (hi := (581453761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111817) = 1/(111817 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-581453761 / 1000000000) (-1817043 / 3125000) (Real.log (111817 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73178189 / 200000000) ≤ -Real.log (500000 / 720899) ∧
    -Real.log (500000 / 720899) ≤ (182945473 / 500000000) := by
  have h := checkLog_sound (w := (220899 / 1220899)) (n := 12)
    (lo := (73178189 / 200000000)) (hi := (182945473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720899 / 500000) = 1/(500000 / 720899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73178189 / 200000000) (182945473 / 500000000) (Real.log (720899 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (720899 / 500000) = -Real.log (500000 / 720899) := by
    rw [show ((720899 / 500000) : ℝ) = ((500000 / 720899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (291517187 / 500000000) ≤ -Real.log (279101 / 500000) ∧
    -Real.log (279101 / 500000) ≤ (186571 / 320000) := by
  have h := checkLog_sound (w := (220899 / 779101)) (n := 12)
    (lo := (291517187 / 500000000)) (hi := (186571 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279101) = 1/(279101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-186571 / 320000) (-291517187 / 500000000) (Real.log (279101 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (284777357 / 1000000000) ≤ -Real.log (500000 / 664733) ∧
    -Real.log (500000 / 664733) ≤ (142388679 / 500000000) := by
  have h := checkLog_sound (w := (164733 / 1164733)) (n := 12)
    (lo := (284777357 / 1000000000)) (hi := (142388679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664733 / 500000) = 1/(500000 / 664733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (284777357 / 1000000000) (142388679 / 500000000) (Real.log (664733 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (664733 / 500000) = -Real.log (500000 / 664733) := by
    rw [show ((664733 / 500000) : ℝ) = ((500000 / 664733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (399680869 / 1000000000) ≤ -Real.log (335267 / 500000) ∧
    -Real.log (335267 / 500000) ≤ (39968087 / 100000000) := by
  have h := checkLog_sound (w := (164733 / 835267)) (n := 12)
    (lo := (399680869 / 1000000000)) (hi := (39968087 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335267) = 1/(335267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-39968087 / 100000000) (-399680869 / 1000000000) (Real.log (335267 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (142665029 / 500000000) ≤ -Real.log (1000000 / 1330201) ∧
    -Real.log (1000000 / 1330201) ≤ (285330059 / 1000000000) := by
  have h := checkLog_sound (w := (330201 / 2330201)) (n := 12)
    (lo := (142665029 / 500000000)) (hi := (285330059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330201 / 1000000) = 1/(1000000 / 1330201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142665029 / 500000000) (285330059 / 1000000000) (Real.log (1330201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1330201 / 1000000) = -Real.log (1000000 / 1330201) := by
    rw [show ((1330201 / 1000000) : ℝ) = ((1000000 / 1330201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (400777611 / 1000000000) ≤ -Real.log (669799 / 1000000) ∧
    -Real.log (669799 / 1000000) ≤ (100194403 / 250000000) := by
  have h := checkLog_sound (w := (330201 / 1669799)) (n := 12)
    (lo := (400777611 / 1000000000)) (hi := (100194403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669799) = 1/(669799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-100194403 / 250000000) (-400777611 / 1000000000) (Real.log (669799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118341511 / 125000000) ≤ -Real.log (50000000000 / 128863679047) ∧
    -Real.log (50000000000 / 128863679047) ≤ (94673209 / 100000000) := by
  have h := checkLog_sound (w := (28863679047 / 228863679047)) (n := 12)
    (lo := (63396227 / 250000000)) (hi := (253584909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128863679047 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128863679047 / 100000000000) = 1/(50000000000 / 128863679047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118341511 / 125000000) (94673209 / 100000000) (Real.log (128863679047 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (128863679047 / 50000000000) = -Real.log (50000000000 / 128863679047) := by
    rw [show ((128863679047 / 50000000000) : ℝ) = ((50000000000 / 128863679047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23723133 / 25000000) ≤ -Real.log (100000000000 / 258293234349) ∧
    -Real.log (100000000000 / 258293234349) ≤ (474462661 / 500000000) := by
  have h := checkLog_sound (w := (58293234349 / 458293234349)) (n := 12)
    (lo := (12788907 / 50000000)) (hi := (255778141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258293234349 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(258293234349 / 200000000000) = 1/(100000000000 / 258293234349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23723133 / 25000000) (474462661 / 500000000) (Real.log (258293234349 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (258293234349 / 100000000000) = -Real.log (100000000000 / 258293234349) := by
    rw [show ((258293234349 / 100000000000) : ℝ) = ((100000000000 / 258293234349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (342229113 / 500000000) ≤ -Real.log (50000000000 / 99134868627) ∧
    -Real.log (50000000000 / 99134868627) ≤ (684458227 / 1000000000) := by
  have h := checkLog_sound (w := (49134868627 / 149134868627)) (n := 12)
    (lo := (342229113 / 500000000)) (hi := (684458227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99134868627 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99134868627 / 50000000000) = 1/(50000000000 / 99134868627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (342229113 / 500000000) (684458227 / 1000000000) (Real.log (99134868627 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (99134868627 / 50000000000) = -Real.log (50000000000 / 99134868627) := by
    rw [show ((99134868627 / 50000000000) : ℝ) = ((50000000000 / 99134868627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68610767 / 100000000) ≤ -Real.log (125000000000 / 248246302249) ∧
    -Real.log (125000000000 / 248246302249) ≤ (686107671 / 1000000000) := by
  have h := checkLog_sound (w := (123246302249 / 373246302249)) (n := 12)
    (lo := (68610767 / 100000000)) (hi := (686107671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248246302249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248246302249 / 125000000000) = 1/(125000000000 / 248246302249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68610767 / 100000000) (686107671 / 1000000000) (Real.log (248246302249 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (248246302249 / 125000000000) = -Real.log (125000000000 / 248246302249) := by
    rw [show ((248246302249 / 125000000000) : ℝ) = ((125000000000 / 248246302249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0196

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0197Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0197
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

theorem reflection_log_1_neg : (33376363 / 125000000) ≤ -Real.log (5120 / 6687) ∧
    -Real.log (5120 / 6687) ≤ (53402181 / 200000000) := by
  have h := checkLog_sound (w := (1567 / 11807)) (n := 12)
    (lo := (33376363 / 125000000)) (hi := (53402181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6687 / 5120) = 1/(5120 / 6687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33376363 / 125000000) (53402181 / 200000000) (Real.log (6687 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6687 / 5120) = -Real.log (5120 / 6687) := by
    rw [show ((6687 / 5120) : ℝ) = ((5120 / 6687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (182681061 / 500000000) ≤ -Real.log (3553 / 5120) ∧
    -Real.log (3553 / 5120) ≤ (365362123 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 8673)) (n := 12)
    (lo := (182681061 / 500000000)) (hi := (365362123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3553) = 1/(3553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-365362123 / 1000000000) (-182681061 / 500000000) (Real.log (3553 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266562171 / 1000000000) ≤ -Real.log (1280 / 1671) ∧
    -Real.log (1280 / 1671) ≤ (66640543 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2951)) (n := 12)
    (lo := (266562171 / 1000000000)) (hi := (66640543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1280) = 1/(1280 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266562171 / 1000000000) (66640543 / 250000000) (Real.log (1671 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1671 / 1280) = -Real.log (1280 / 1671) := by
    rw [show ((1671 / 1280) : ℝ) = ((1280 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (364518121 / 1000000000) ≤ -Real.log (889 / 1280) ∧
    -Real.log (889 / 1280) ≤ (182259061 / 500000000) := by
  have h := checkLog_sound (w := (391 / 2169)) (n := 12)
    (lo := (364518121 / 1000000000)) (hi := (182259061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 889) = 1/(889 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-182259061 / 500000000) (-364518121 / 1000000000) (Real.log (889 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119385873 / 250000000) ≤ -Real.log (2560 / 4127) ∧
    -Real.log (2560 / 4127) ≤ (477543493 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 6687)) (n := 12)
    (lo := (119385873 / 250000000)) (hi := (477543493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4127 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4127 / 2560) = 1/(2560 / 4127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119385873 / 250000000) (477543493 / 1000000000) (Real.log (4127 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4127 / 2560) = -Real.log (2560 / 4127) := by
    rw [show ((4127 / 2560) : ℝ) = ((2560 / 4127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14797373 / 15625000) ≤ -Real.log (993 / 2560) ∧
    -Real.log (993 / 2560) ≤ (473515937 / 500000000) := by
  have h := checkLog_sound (w := (287 / 2273)) (n := 12)
    (lo := (63471173 / 250000000)) (hi := (253884693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 993) = 1/(993 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-473515937 / 500000000) (-14797373 / 15625000) (Real.log (993 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (476816307 / 1000000000) ≤ -Real.log (640 / 1031) ∧
    -Real.log (640 / 1031) ≤ (119204077 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1671)) (n := 12)
    (lo := (476816307 / 1000000000)) (hi := (119204077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1031 / 640) = 1/(640 / 1031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (476816307 / 1000000000) (119204077 / 250000000) (Real.log (1031 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1031 / 640) = -Real.log (640 / 1031) := by
    rw [show ((1031 / 640) : ℝ) = ((640 / 1031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (944015279 / 1000000000) ≤ -Real.log (249 / 640) ∧
    -Real.log (249 / 640) ≤ (944015281 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 249) = 1/(249 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-944015281 / 1000000000) (-944015279 / 1000000000) (Real.log (249 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91166681 / 250000000) ≤ -Real.log (500000 / 720017) ∧
    -Real.log (500000 / 720017) ≤ (14586669 / 40000000) := by
  have h := checkLog_sound (w := (220017 / 1220017)) (n := 12)
    (lo := (91166681 / 250000000)) (hi := (14586669 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720017 / 500000) = 1/(500000 / 720017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91166681 / 250000000) (14586669 / 40000000) (Real.log (720017 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (720017 / 500000) = -Real.log (500000 / 720017) := by
    rw [show ((720017 / 500000) : ℝ) = ((500000 / 720017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (579879211 / 1000000000) ≤ -Real.log (279983 / 500000) ∧
    -Real.log (279983 / 500000) ≤ (144969803 / 250000000) := by
  have h := checkLog_sound (w := (220017 / 779983)) (n := 12)
    (lo := (579879211 / 1000000000)) (hi := (144969803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279983) = 1/(279983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-144969803 / 250000000) (-579879211 / 1000000000) (Real.log (279983 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182639511 / 500000000) ≤ -Real.log (250000 / 360229) ∧
    -Real.log (250000 / 360229) ≤ (365279023 / 1000000000) := by
  have h := checkLog_sound (w := (110229 / 610229)) (n := 12)
    (lo := (182639511 / 500000000)) (hi := (365279023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360229 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360229 / 250000) = 1/(250000 / 360229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182639511 / 500000000) (365279023 / 1000000000) (Real.log (360229 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (360229 / 250000) = -Real.log (250000 / 360229) := by
    rw [show ((360229 / 250000) : ℝ) = ((250000 / 360229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145363887 / 250000000) ≤ -Real.log (139771 / 250000) ∧
    -Real.log (139771 / 250000) ≤ (581455549 / 1000000000) := by
  have h := checkLog_sound (w := (110229 / 389771)) (n := 12)
    (lo := (145363887 / 250000000)) (hi := (581455549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139771) = 1/(139771 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-581455549 / 1000000000) (-145363887 / 250000000) (Real.log (139771 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4441029 / 15625000) ≤ -Real.log (1000000 / 1328733) ∧
    -Real.log (1000000 / 1328733) ≤ (284225857 / 1000000000) := by
  have h := checkLog_sound (w := (328733 / 2328733)) (n := 12)
    (lo := (4441029 / 15625000)) (hi := (284225857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328733 / 1000000) = 1/(1000000 / 1328733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4441029 / 15625000) (284225857 / 1000000000) (Real.log (1328733 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1328733 / 1000000) = -Real.log (1000000 / 1328733) := by
    rw [show ((1328733 / 1000000) : ℝ) = ((1000000 / 1328733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (398588307 / 1000000000) ≤ -Real.log (671267 / 1000000) ∧
    -Real.log (671267 / 1000000) ≤ (99647077 / 250000000) := by
  have h := checkLog_sound (w := (328733 / 1671267)) (n := 12)
    (lo := (398588307 / 1000000000)) (hi := (99647077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671267) = 1/(671267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-99647077 / 250000000) (-398588307 / 1000000000) (Real.log (671267 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28477811 / 100000000) ≤ -Real.log (1000000 / 1329467) ∧
    -Real.log (1000000 / 1329467) ≤ (284778111 / 1000000000) := by
  have h := checkLog_sound (w := (329467 / 2329467)) (n := 12)
    (lo := (28477811 / 100000000)) (hi := (284778111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329467 / 1000000) = 1/(1000000 / 1329467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28477811 / 100000000) (284778111 / 1000000000) (Real.log (1329467 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1329467 / 1000000) = -Real.log (1000000 / 1329467) := by
    rw [show ((1329467 / 1000000) : ℝ) = ((1000000 / 1329467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (9992059 / 25000000) ≤ -Real.log (670533 / 1000000) ∧
    -Real.log (670533 / 1000000) ≤ (399682361 / 1000000000) := by
  have h := checkLog_sound (w := (329467 / 1670533)) (n := 12)
    (lo := (9992059 / 25000000)) (hi := (399682361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670533) = 1/(670533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-399682361 / 1000000000) (-9992059 / 25000000) (Real.log (670533 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (188909187 / 200000000) ≤ -Real.log (62500000000 / 160727838833) ∧
    -Real.log (62500000000 / 160727838833) ≤ (944545937 / 1000000000) := by
  have h := checkLog_sound (w := (35727838833 / 285727838833)) (n := 12)
    (lo := (50279751 / 200000000)) (hi := (62849689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160727838833 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160727838833 / 125000000000) = 1/(62500000000 / 160727838833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188909187 / 200000000) (944545937 / 1000000000) (Real.log (160727838833 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (160727838833 / 62500000000) = -Real.log (62500000000 / 160727838833) := by
    rw [show ((160727838833 / 62500000000) : ℝ) = ((62500000000 / 160727838833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (94673457 / 100000000) ≤ -Real.log (250000000000 / 644319994849) ∧
    -Real.log (250000000000 / 644319994849) ≤ (236683643 / 250000000) := by
  have h := checkLog_sound (w := (144319994849 / 1144319994849)) (n := 12)
    (lo := (25358739 / 100000000)) (hi := (253587391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644319994849 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(644319994849 / 500000000000) = 1/(250000000000 / 644319994849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (94673457 / 100000000) (236683643 / 250000000) (Real.log (644319994849 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (644319994849 / 250000000000) = -Real.log (250000000000 / 644319994849) := by
    rw [show ((644319994849 / 250000000000) : ℝ) = ((250000000000 / 644319994849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (170703541 / 250000000) ≤ -Real.log (500000000000 / 989720185857) ∧
    -Real.log (500000000000 / 989720185857) ≤ (136562833 / 200000000) := by
  have h := checkLog_sound (w := (489720185857 / 1489720185857)) (n := 12)
    (lo := (170703541 / 250000000)) (hi := (136562833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989720185857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989720185857 / 500000000000) = 1/(500000000000 / 989720185857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (170703541 / 250000000) (136562833 / 200000000) (Real.log (989720185857 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (989720185857 / 500000000000) = -Real.log (500000000000 / 989720185857) := by
    rw [show ((989720185857 / 500000000000) : ℝ) = ((500000000000 / 989720185857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68446047 / 100000000) ≤ -Real.log (125000000000 / 247837727599) ∧
    -Real.log (125000000000 / 247837727599) ≤ (684460471 / 1000000000) := by
  have h := checkLog_sound (w := (122837727599 / 372837727599)) (n := 12)
    (lo := (68446047 / 100000000)) (hi := (684460471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247837727599 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247837727599 / 125000000000) = 1/(125000000000 / 247837727599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68446047 / 100000000) (684460471 / 1000000000) (Real.log (247837727599 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (247837727599 / 125000000000) = -Real.log (125000000000 / 247837727599) := by
    rw [show ((247837727599 / 125000000000) : ℝ) = ((125000000000 / 247837727599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0197

end


