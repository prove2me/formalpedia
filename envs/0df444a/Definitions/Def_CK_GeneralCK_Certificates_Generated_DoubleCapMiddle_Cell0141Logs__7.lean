-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0141Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0141Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:14:56.591446+00:00
-- url     : https://prove2.me/theorems/b0c2497a-71e9-4eb0-84cd-0aff33a3be2a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0141Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0142Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0141Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0144Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0145Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0147Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0141Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0144Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0145Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0147Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0141Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0144Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0145Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0147Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0141Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0142Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0143Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0144Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0145Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0146Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0147Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0141Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0141
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

theorem reflection_log_1_neg : (74591743 / 250000000) ≤ -Real.log (256 / 345) ∧
    -Real.log (256 / 345) ≤ (298366973 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 601)) (n := 12)
    (lo := (74591743 / 250000000)) (hi := (298366973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345 / 256) = 1/(256 / 345) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (74591743 / 250000000) (298366973 / 1000000000) (Real.log (345 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (345 / 256) = -Real.log (256 / 345) := by
    rw [show ((345 / 256) : ℝ) = ((256 / 345) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26698977 / 62500000) ≤ -Real.log (167 / 256) ∧
    -Real.log (167 / 256) ≤ (427183633 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 423)) (n := 12)
    (lo := (26698977 / 62500000)) (hi := (427183633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 167) = 1/(167 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-427183633 / 1000000000) (-26698977 / 62500000) (Real.log (167 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (297497029 / 1000000000) ≤ -Real.log (2560 / 3447) ∧
    -Real.log (2560 / 3447) ≤ (29749703 / 100000000) := by
  have h := checkLog_sound (w := (887 / 6007)) (n := 12)
    (lo := (297497029 / 1000000000)) (hi := (29749703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3447 / 2560) = 1/(2560 / 3447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (297497029 / 1000000000) (29749703 / 100000000) (Real.log (3447 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3447 / 2560) = -Real.log (2560 / 3447) := by
    rw [show ((3447 / 2560) : ℝ) = ((2560 / 3447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (106347209 / 250000000) ≤ -Real.log (1673 / 2560) ∧
    -Real.log (1673 / 2560) ≤ (425388837 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 4233)) (n := 12)
    (lo := (106347209 / 250000000)) (hi := (425388837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1673) = 1/(1673 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-425388837 / 1000000000) (-106347209 / 250000000) (Real.log (1673 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (527867089 / 1000000000) ≤ -Real.log (128 / 217) ∧
    -Real.log (128 / 217) ≤ (52786709 / 100000000) := by
  have h := checkLog_sound (w := (89 / 345)) (n := 12)
    (lo := (527867089 / 1000000000)) (hi := (52786709 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217 / 128) = 1/(128 / 217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (527867089 / 1000000000) (52786709 / 100000000) (Real.log (217 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (217 / 128) = -Real.log (128 / 217) := by
    rw [show ((217 / 128) : ℝ) = ((128 / 217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1188468617 / 1000000000) ≤ -Real.log (39 / 128) ∧
    -Real.log (39 / 128) ≤ (1188468619 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 39) = 1/(39 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1188468619 / 1000000000) (-1188468617 / 1000000000) (Real.log (39 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131620911 / 250000000) ≤ -Real.log (1280 / 2167) ∧
    -Real.log (1280 / 2167) ≤ (105296729 / 200000000) := by
  have h := checkLog_sound (w := (887 / 3447)) (n := 12)
    (lo := (131620911 / 250000000)) (hi := (105296729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2167 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2167 / 1280) = 1/(1280 / 2167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131620911 / 250000000) (105296729 / 200000000) (Real.log (2167 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2167 / 1280) = -Real.log (1280 / 2167) := by
    rw [show ((2167 / 1280) : ℝ) = ((1280 / 2167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (73800359 / 62500000) ≤ -Real.log (393 / 1280) ∧
    -Real.log (393 / 1280) ≤ (590402873 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 393) = 1/(393 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-590402873 / 500000000) (-73800359 / 62500000) (Real.log (393 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (407135711 / 1000000000) ≤ -Real.log (250000 / 375627) ∧
    -Real.log (250000 / 375627) ≤ (12722991 / 31250000) := by
  have h := checkLog_sound (w := (125627 / 625627)) (n := 12)
    (lo := (407135711 / 1000000000)) (hi := (12722991 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375627 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375627 / 250000) = 1/(250000 / 375627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (407135711 / 1000000000) (12722991 / 31250000) (Real.log (375627 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (375627 / 250000) = -Real.log (250000 / 375627) := by
    rw [show ((375627 / 250000) : ℝ) = ((250000 / 375627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349087901 / 500000000) ≤ -Real.log (124373 / 250000) ∧
    -Real.log (124373 / 250000) ≤ (174543951 / 250000000) := by
  have h := checkLog_sound (w := (627 / 249373)) (n := 12)
    (lo := (2514311 / 500000000)) (hi := (5028623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124373) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 124373) = 1/(124373 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174543951 / 250000000) (-349087901 / 500000000) (Real.log (124373 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51042621 / 125000000) ≤ -Real.log (3125 / 4701) ∧
    -Real.log (3125 / 4701) ≤ (408340969 / 1000000000) := by
  have h := checkLog_sound (w := (788 / 3913)) (n := 12)
    (lo := (51042621 / 125000000)) (hi := (408340969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4701 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4701 / 3125) = 1/(3125 / 4701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51042621 / 125000000) (408340969 / 1000000000) (Real.log (4701 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4701 / 3125) = -Real.log (3125 / 4701) := by
    rw [show ((4701 / 3125) : ℝ) = ((3125 / 4701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (701824721 / 1000000000) ≤ -Real.log (1549 / 3125) ∧
    -Real.log (1549 / 3125) ≤ (701824723 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 6223)) (n := 12)
    (lo := (8677541 / 1000000000)) (hi := (4338771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3098) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 3098) = 1/(1549 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-701824723 / 1000000000) (-701824721 / 1000000000) (Real.log (1549 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323476007 / 1000000000) ≤ -Real.log (1000000 / 1381923) ∧
    -Real.log (1000000 / 1381923) ≤ (40434501 / 125000000) := by
  have h := checkLog_sound (w := (381923 / 2381923)) (n := 12)
    (lo := (323476007 / 1000000000)) (hi := (40434501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381923 / 1000000) = 1/(1000000 / 1381923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323476007 / 1000000000) (40434501 / 125000000) (Real.log (1381923 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1381923 / 1000000) = -Real.log (1000000 / 1381923) := by
    rw [show ((1381923 / 1000000) : ℝ) = ((1000000 / 1381923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (481142233 / 1000000000) ≤ -Real.log (618077 / 1000000) ∧
    -Real.log (618077 / 1000000) ≤ (240571117 / 500000000) := by
  have h := checkLog_sound (w := (381923 / 1618077)) (n := 12)
    (lo := (481142233 / 1000000000)) (hi := (240571117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618077) = 1/(618077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-240571117 / 500000000) (-481142233 / 1000000000) (Real.log (618077 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (324620857 / 1000000000) ≤ -Real.log (500000 / 691753) ∧
    -Real.log (500000 / 691753) ≤ (162310429 / 500000000) := by
  have h := checkLog_sound (w := (191753 / 1191753)) (n := 12)
    (lo := (324620857 / 1000000000)) (hi := (162310429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691753 / 500000) = 1/(500000 / 691753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (324620857 / 1000000000) (162310429 / 500000000) (Real.log (691753 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (691753 / 500000) = -Real.log (500000 / 691753) := by
    rw [show ((691753 / 500000) : ℝ) = ((500000 / 691753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7557917 / 15625000) ≤ -Real.log (308247 / 500000) ∧
    -Real.log (308247 / 500000) ≤ (483706689 / 1000000000) := by
  have h := checkLog_sound (w := (191753 / 808247)) (n := 12)
    (lo := (7557917 / 15625000)) (hi := (483706689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308247) = 1/(308247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-483706689 / 1000000000) (-7557917 / 15625000) (Real.log (308247 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (552655757 / 500000000) ≤ -Real.log (31250000000 / 94380160887) ∧
    -Real.log (31250000000 / 94380160887) ≤ (276327879 / 250000000) := by
  have h := checkLog_sound (w := (31880160887 / 156880160887)) (n := 12)
    (lo := (206082167 / 500000000)) (hi := (82432867 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94380160887 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94380160887 / 62500000000) = 1/(31250000000 / 94380160887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (552655757 / 500000000) (276327879 / 250000000) (Real.log (94380160887 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (94380160887 / 31250000000) = -Real.log (31250000000 / 94380160887) := by
    rw [show ((94380160887 / 31250000000) : ℝ) = ((31250000000 / 94380160887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (111016569 / 100000000) ≤ -Real.log (125000000000 / 379357650097) ∧
    -Real.log (125000000000 / 379357650097) ≤ (277541423 / 250000000) := by
  have h := checkLog_sound (w := (129357650097 / 629357650097)) (n := 12)
    (lo := (41701851 / 100000000)) (hi := (417018511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379357650097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(379357650097 / 250000000000) = 1/(125000000000 / 379357650097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (111016569 / 100000000) (277541423 / 250000000) (Real.log (379357650097 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (379357650097 / 125000000000) = -Real.log (125000000000 / 379357650097) := by
    rw [show ((379357650097 / 125000000000) : ℝ) = ((125000000000 / 379357650097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (314304 / 390625) ≤ -Real.log (500000000000 / 1117921391671) ∧
    -Real.log (500000000000 / 1117921391671) ≤ (402309121 / 500000000) := by
  have h := checkLog_sound (w := (117921391671 / 2117921391671)) (n := 12)
    (lo := (5573553 / 50000000)) (hi := (111471061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117921391671 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1117921391671 / 1000000000000) = 1/(500000000000 / 1117921391671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (314304 / 390625) (402309121 / 500000000) (Real.log (1117921391671 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1117921391671 / 500000000000) = -Real.log (500000000000 / 1117921391671) := by
    rw [show ((1117921391671 / 500000000000) : ℝ) = ((500000000000 / 1117921391671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (161665509 / 200000000) ≤ -Real.log (500000000000 / 1122075802847) ∧
    -Real.log (500000000000 / 1122075802847) ≤ (808327547 / 1000000000) := by
  have h := checkLog_sound (w := (122075802847 / 2122075802847)) (n := 12)
    (lo := (23036073 / 200000000)) (hi := (57590183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122075802847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122075802847 / 1000000000000) = 1/(500000000000 / 1122075802847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (161665509 / 200000000) (808327547 / 1000000000) (Real.log (1122075802847 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1122075802847 / 500000000000) = -Real.log (500000000000 / 1122075802847) := by
    rw [show ((1122075802847 / 500000000000) : ℝ) = ((500000000000 / 1122075802847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0141

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0142Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0142
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

theorem reflection_log_1_neg : (297497029 / 1000000000) ≤ -Real.log (2560 / 3447) ∧
    -Real.log (2560 / 3447) ≤ (29749703 / 100000000) := by
  have h := checkLog_sound (w := (887 / 6007)) (n := 12)
    (lo := (297497029 / 1000000000)) (hi := (29749703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3447 / 2560) = 1/(2560 / 3447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (297497029 / 1000000000) (29749703 / 100000000) (Real.log (3447 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3447 / 2560) = -Real.log (2560 / 3447) := by
    rw [show ((3447 / 2560) : ℝ) = ((2560 / 3447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (106347209 / 250000000) ≤ -Real.log (1673 / 2560) ∧
    -Real.log (1673 / 2560) ≤ (425388837 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 4233)) (n := 12)
    (lo := (106347209 / 250000000)) (hi := (425388837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1673) = 1/(1673 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-425388837 / 1000000000) (-106347209 / 250000000) (Real.log (1673 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37078291 / 125000000) ≤ -Real.log (640 / 861) ∧
    -Real.log (640 / 861) ≤ (296626329 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1501)) (n := 12)
    (lo := (37078291 / 125000000)) (hi := (296626329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 640) = 1/(640 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37078291 / 125000000) (296626329 / 1000000000) (Real.log (861 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (861 / 640) = -Real.log (640 / 861) := by
    rw [show ((861 / 640) : ℝ) = ((640 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52949657 / 125000000) ≤ -Real.log (419 / 640) ∧
    -Real.log (419 / 640) ≤ (423597257 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1059)) (n := 12)
    (lo := (52949657 / 125000000)) (hi := (423597257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 419) = 1/(419 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-423597257 / 1000000000) (-52949657 / 125000000) (Real.log (419 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131620911 / 250000000) ≤ -Real.log (1280 / 2167) ∧
    -Real.log (1280 / 2167) ≤ (105296729 / 200000000) := by
  have h := checkLog_sound (w := (887 / 3447)) (n := 12)
    (lo := (131620911 / 250000000)) (hi := (105296729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2167 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2167 / 1280) = 1/(1280 / 2167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131620911 / 250000000) (105296729 / 200000000) (Real.log (2167 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2167 / 1280) = -Real.log (1280 / 2167) := by
    rw [show ((2167 / 1280) : ℝ) = ((1280 / 2167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (73800359 / 62500000) ≤ -Real.log (393 / 1280) ∧
    -Real.log (393 / 1280) ≤ (590402873 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 393) = 1/(393 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-590402873 / 500000000) (-73800359 / 62500000) (Real.log (393 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (525098283 / 1000000000) ≤ -Real.log (320 / 541) ∧
    -Real.log (320 / 541) ≤ (131274571 / 250000000) := by
  have h := checkLog_sound (w := (221 / 861)) (n := 12)
    (lo := (525098283 / 1000000000)) (hi := (131274571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541 / 320) = 1/(320 / 541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (525098283 / 1000000000) (131274571 / 250000000) (Real.log (541 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (541 / 320) = -Real.log (320 / 541) := by
    rw [show ((541 / 320) : ℝ) = ((320 / 541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (234640229 / 200000000) ≤ -Real.log (99 / 320) ∧
    -Real.log (99 / 320) ≤ (1173201147 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 99) = 1/(99 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1173201147 / 1000000000) (-234640229 / 200000000) (Real.log (99 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (405930333 / 1000000000) ≤ -Real.log (500000 / 750349) ∧
    -Real.log (500000 / 750349) ≤ (202965167 / 500000000) := by
  have h := checkLog_sound (w := (250349 / 1250349)) (n := 12)
    (lo := (405930333 / 1000000000)) (hi := (202965167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750349 / 500000) = 1/(500000 / 750349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (405930333 / 1000000000) (202965167 / 500000000) (Real.log (750349 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (750349 / 500000) = -Real.log (500000 / 750349) := by
    rw [show ((750349 / 500000) : ℝ) = ((500000 / 750349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (138908831 / 200000000) ≤ -Real.log (249651 / 500000) ∧
    -Real.log (249651 / 500000) ≤ (694544157 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 499651)) (n := 12)
    (lo := (55879 / 40000000)) (hi := (87311 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249651) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 249651) = 1/(249651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-694544157 / 1000000000) (-138908831 / 200000000) (Real.log (249651 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (407136377 / 1000000000) ≤ -Real.log (1000000 / 1502509) ∧
    -Real.log (1000000 / 1502509) ≤ (203568189 / 500000000) := by
  have h := checkLog_sound (w := (502509 / 2502509)) (n := 12)
    (lo := (407136377 / 1000000000)) (hi := (203568189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502509 / 1000000) = 1/(1000000 / 1502509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (407136377 / 1000000000) (203568189 / 500000000) (Real.log (1502509 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1502509 / 1000000) = -Real.log (1000000 / 1502509) := by
    rw [show ((1502509 / 1000000) : ℝ) = ((1000000 / 1502509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174544453 / 250000000) ≤ -Real.log (497491 / 1000000) ∧
    -Real.log (497491 / 1000000) ≤ (349088907 / 500000000) := by
  have h := checkLog_sound (w := (2509 / 997491)) (n := 12)
    (lo := (628829 / 125000000)) (hi := (5030633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497491) = 1/(497491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349088907 / 500000000) (-174544453 / 250000000) (Real.log (497491 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (322333467 / 1000000000) ≤ -Real.log (200000 / 276069) ∧
    -Real.log (200000 / 276069) ≤ (80583367 / 250000000) := by
  have h := checkLog_sound (w := (76069 / 476069)) (n := 12)
    (lo := (322333467 / 1000000000)) (hi := (80583367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276069 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276069 / 200000) = 1/(200000 / 276069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (322333467 / 1000000000) (80583367 / 250000000) (Real.log (276069 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (276069 / 200000) = -Real.log (200000 / 276069) := by
    rw [show ((276069 / 200000) : ℝ) = ((200000 / 276069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (478592407 / 1000000000) ≤ -Real.log (123931 / 200000) ∧
    -Real.log (123931 / 200000) ≤ (59824051 / 125000000) := by
  have h := checkLog_sound (w := (76069 / 323931)) (n := 12)
    (lo := (478592407 / 1000000000)) (hi := (59824051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123931) = 1/(123931 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59824051 / 125000000) (-478592407 / 1000000000) (Real.log (123931 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323476731 / 1000000000) ≤ -Real.log (250000 / 345481) ∧
    -Real.log (250000 / 345481) ≤ (80869183 / 250000000) := by
  have h := checkLog_sound (w := (95481 / 595481)) (n := 12)
    (lo := (323476731 / 1000000000)) (hi := (80869183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345481 / 250000) = 1/(250000 / 345481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323476731 / 1000000000) (80869183 / 250000000) (Real.log (345481 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (345481 / 250000) = -Real.log (250000 / 345481) := by
    rw [show ((345481 / 250000) : ℝ) = ((250000 / 345481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (481143851 / 1000000000) ≤ -Real.log (154519 / 250000) ∧
    -Real.log (154519 / 250000) ≤ (120285963 / 250000000) := by
  have h := checkLog_sound (w := (95481 / 404519)) (n := 12)
    (lo := (481143851 / 1000000000)) (hi := (120285963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154519) = 1/(154519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120285963 / 250000000) (-481143851 / 1000000000) (Real.log (154519 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (137559311 / 125000000) ≤ -Real.log (12500000000 / 37569897577) ∧
    -Real.log (12500000000 / 37569897577) ≤ (110047449 / 100000000) := by
  have h := checkLog_sound (w := (12569897577 / 62569897577)) (n := 12)
    (lo := (101831827 / 250000000)) (hi := (407327309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37569897577 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37569897577 / 25000000000) = 1/(12500000000 / 37569897577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (137559311 / 125000000) (110047449 / 100000000) (Real.log (37569897577 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (37569897577 / 12500000000) = -Real.log (12500000000 / 37569897577) := by
    rw [show ((37569897577 / 12500000000) : ℝ) = ((12500000000 / 37569897577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1105314189 / 1000000000) ≤ -Real.log (500000000000 / 1510086614633) ∧
    -Real.log (500000000000 / 1510086614633) ≤ (1105314191 / 1000000000) := by
  have h := checkLog_sound (w := (510086614633 / 2510086614633)) (n := 12)
    (lo := (412167009 / 1000000000)) (hi := (41216701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510086614633 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1510086614633 / 1000000000000) = 1/(500000000000 / 1510086614633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1105314189 / 1000000000) (1105314191 / 1000000000) (Real.log (1510086614633 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1510086614633 / 500000000000) = -Real.log (500000000000 / 1510086614633) := by
    rw [show ((1510086614633 / 500000000000) : ℝ) = ((500000000000 / 1510086614633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (400462937 / 500000000) ≤ -Real.log (250000000000 / 556900614051) ∧
    -Real.log (250000000000 / 556900614051) ≤ (200231469 / 250000000) := by
  have h := checkLog_sound (w := (56900614051 / 1056900614051)) (n := 12)
    (lo := (53889347 / 500000000)) (hi := (21555739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556900614051 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556900614051 / 500000000000) = 1/(250000000000 / 556900614051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (400462937 / 500000000) (200231469 / 250000000) (Real.log (556900614051 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (556900614051 / 250000000000) = -Real.log (250000000000 / 556900614051) := by
    rw [show ((556900614051 / 250000000000) : ℝ) = ((250000000000 / 556900614051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (402310291 / 500000000) ≤ -Real.log (250000000000 / 558962004673) ∧
    -Real.log (250000000000 / 558962004673) ≤ (100577573 / 125000000) := by
  have h := checkLog_sound (w := (58962004673 / 1058962004673)) (n := 12)
    (lo := (55736701 / 500000000)) (hi := (111473403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558962004673 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558962004673 / 500000000000) = 1/(250000000000 / 558962004673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (402310291 / 500000000) (100577573 / 125000000) (Real.log (558962004673 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (558962004673 / 250000000000) = -Real.log (250000000000 / 558962004673) := by
    rw [show ((558962004673 / 250000000000) : ℝ) = ((250000000000 / 558962004673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0142

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0143Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0143
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

theorem reflection_log_1_neg : (37078291 / 125000000) ≤ -Real.log (640 / 861) ∧
    -Real.log (640 / 861) ≤ (296626329 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1501)) (n := 12)
    (lo := (37078291 / 125000000)) (hi := (296626329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 640) = 1/(640 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37078291 / 125000000) (296626329 / 1000000000) (Real.log (861 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (861 / 640) = -Real.log (640 / 861) := by
    rw [show ((861 / 640) : ℝ) = ((640 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52949657 / 125000000) ≤ -Real.log (419 / 640) ∧
    -Real.log (419 / 640) ≤ (423597257 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1059)) (n := 12)
    (lo := (52949657 / 125000000)) (hi := (423597257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 419) = 1/(419 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-423597257 / 1000000000) (-52949657 / 125000000) (Real.log (419 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73938717 / 250000000) ≤ -Real.log (2560 / 3441) ∧
    -Real.log (2560 / 3441) ≤ (295754869 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 6001)) (n := 12)
    (lo := (73938717 / 250000000)) (hi := (295754869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3441 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3441 / 2560) = 1/(2560 / 3441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73938717 / 250000000) (295754869 / 1000000000) (Real.log (3441 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3441 / 2560) = -Real.log (2560 / 3441) := by
    rw [show ((3441 / 2560) : ℝ) = ((2560 / 3441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5272611 / 12500000) ≤ -Real.log (1679 / 2560) ∧
    -Real.log (1679 / 2560) ≤ (421808881 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 4239)) (n := 12)
    (lo := (5272611 / 12500000)) (hi := (421808881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1679) = 1/(1679 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-421808881 / 1000000000) (-5272611 / 12500000) (Real.log (1679 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (525098283 / 1000000000) ≤ -Real.log (320 / 541) ∧
    -Real.log (320 / 541) ≤ (131274571 / 250000000) := by
  have h := checkLog_sound (w := (221 / 861)) (n := 12)
    (lo := (525098283 / 1000000000)) (hi := (131274571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541 / 320) = 1/(320 / 541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (525098283 / 1000000000) (131274571 / 250000000) (Real.log (541 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (541 / 320) = -Real.log (320 / 541) := by
    rw [show ((541 / 320) : ℝ) = ((320 / 541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (234640229 / 200000000) ≤ -Real.log (99 / 320) ∧
    -Real.log (99 / 320) ≤ (1173201147 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 99) = 1/(99 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1173201147 / 1000000000) (-234640229 / 200000000) (Real.log (99 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (523710999 / 1000000000) ≤ -Real.log (1280 / 2161) ∧
    -Real.log (1280 / 2161) ≤ (523711 / 1000000) := by
  have h := checkLog_sound (w := (881 / 3441)) (n := 12)
    (lo := (523710999 / 1000000000)) (hi := (523711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2161 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2161 / 1280) = 1/(1280 / 2161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (523710999 / 1000000000) (523711 / 1000000) (Real.log (2161 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2161 / 1280) = -Real.log (1280 / 2161) := by
    rw [show ((2161 / 1280) : ℝ) = ((1280 / 2161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1165653939 / 1000000000) ≤ -Real.log (399 / 1280) ∧
    -Real.log (399 / 1280) ≤ (1165653941 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 399) = 1/(399 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1165653941 / 1000000000) (-1165653939 / 1000000000) (Real.log (399 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (404725501 / 1000000000) ≤ -Real.log (1000000 / 1498891) ∧
    -Real.log (1000000 / 1498891) ≤ (202362751 / 500000000) := by
  have h := checkLog_sound (w := (498891 / 2498891)) (n := 12)
    (lo := (404725501 / 1000000000)) (hi := (202362751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1498891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1498891 / 1000000) = 1/(1000000 / 1498891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (404725501 / 1000000000) (202362751 / 500000000) (Real.log (1498891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1498891 / 1000000) = -Real.log (1000000 / 1498891) := by
    rw [show ((1498891 / 1000000) : ℝ) = ((1000000 / 1498891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (172732909 / 250000000) ≤ -Real.log (501109 / 1000000) ∧
    -Real.log (501109 / 1000000) ≤ (690931637 / 1000000000) := by
  have h := checkLog_sound (w := (498891 / 1501109)) (n := 12)
    (lo := (172732909 / 250000000)) (hi := (690931637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 501109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 501109) = 1/(501109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-690931637 / 1000000000) (-172732909 / 250000000) (Real.log (501109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (405930999 / 1000000000) ≤ -Real.log (1000000 / 1500699) ∧
    -Real.log (1000000 / 1500699) ≤ (405931 / 1000000) := by
  have h := checkLog_sound (w := (500699 / 2500699)) (n := 12)
    (lo := (405930999 / 1000000000)) (hi := (405931 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1500699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1500699 / 1000000) = 1/(1000000 / 1500699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (405930999 / 1000000000) (405931 / 1000000) (Real.log (1500699 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1500699 / 1000000) = -Real.log (1000000 / 1500699) := by
    rw [show ((1500699 / 1000000) : ℝ) = ((1000000 / 1500699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347273079 / 500000000) ≤ -Real.log (499301 / 1000000) ∧
    -Real.log (499301 / 1000000) ≤ (8681827 / 12500000) := by
  have h := checkLog_sound (w := (699 / 999301)) (n := 12)
    (lo := (699489 / 500000000)) (hi := (1398979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 499301) = 1/(499301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8681827 / 12500000) (-347273079 / 500000000) (Real.log (499301 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (321191797 / 1000000000) ≤ -Real.log (100000 / 137877) ∧
    -Real.log (100000 / 137877) ≤ (160595899 / 500000000) := by
  have h := checkLog_sound (w := (37877 / 237877)) (n := 12)
    (lo := (321191797 / 1000000000)) (hi := (160595899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137877 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137877 / 100000) = 1/(100000 / 137877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (321191797 / 1000000000) (160595899 / 500000000) (Real.log (137877 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (137877 / 100000) = -Real.log (100000 / 137877) := by
    rw [show ((137877 / 100000) : ℝ) = ((100000 / 137877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (95210779 / 200000000) ≤ -Real.log (62123 / 100000) ∧
    -Real.log (62123 / 100000) ≤ (59506737 / 125000000) := by
  have h := checkLog_sound (w := (37877 / 162123)) (n := 12)
    (lo := (95210779 / 200000000)) (hi := (59506737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62123) = 1/(62123 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59506737 / 125000000) (-95210779 / 200000000) (Real.log (62123 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20145887 / 62500000) ≤ -Real.log (500000 / 690173) ∧
    -Real.log (500000 / 690173) ≤ (322334193 / 1000000000) := by
  have h := checkLog_sound (w := (190173 / 1190173)) (n := 12)
    (lo := (20145887 / 62500000)) (hi := (322334193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690173 / 500000) = 1/(500000 / 690173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20145887 / 62500000) (322334193 / 1000000000) (Real.log (690173 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (690173 / 500000) = -Real.log (500000 / 690173) := by
    rw [show ((690173 / 500000) : ℝ) = ((500000 / 690173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (478594021 / 1000000000) ≤ -Real.log (309827 / 500000) ∧
    -Real.log (309827 / 500000) ≤ (239297011 / 500000000) := by
  have h := checkLog_sound (w := (190173 / 809827)) (n := 12)
    (lo := (478594021 / 1000000000)) (hi := (239297011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 309827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 309827) = 1/(309827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-239297011 / 500000000) (-478594021 / 1000000000) (Real.log (309827 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1095657137 / 1000000000) ≤ -Real.log (500000000000 / 1495573817273) ∧
    -Real.log (500000000000 / 1495573817273) ≤ (1095657139 / 1000000000) := by
  have h := checkLog_sound (w := (495573817273 / 2495573817273)) (n := 12)
    (lo := (402509957 / 1000000000)) (hi := (201254979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495573817273 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495573817273 / 1000000000000) = 1/(500000000000 / 1495573817273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1095657137 / 1000000000) (1095657139 / 1000000000) (Real.log (1495573817273 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1495573817273 / 500000000000) = -Real.log (500000000000 / 1495573817273) := by
    rw [show ((1495573817273 / 500000000000) : ℝ) = ((500000000000 / 1495573817273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1100477157 / 1000000000) ≤ -Real.log (500000000000 / 1502799914281) ∧
    -Real.log (500000000000 / 1502799914281) ≤ (1100477159 / 1000000000) := by
  have h := checkLog_sound (w := (502799914281 / 2502799914281)) (n := 12)
    (lo := (407329977 / 1000000000)) (hi := (203664989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502799914281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1502799914281 / 1000000000000) = 1/(500000000000 / 1502799914281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1100477157 / 1000000000) (1100477159 / 1000000000) (Real.log (1502799914281 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1502799914281 / 500000000000) = -Real.log (500000000000 / 1502799914281) := by
    rw [show ((1502799914281 / 500000000000) : ℝ) = ((500000000000 / 1502799914281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (199311423 / 250000000) ≤ -Real.log (31250000000 / 69356860583) ∧
    -Real.log (31250000000 / 69356860583) ≤ (398622847 / 500000000) := by
  have h := checkLog_sound (w := (6856860583 / 131856860583)) (n := 12)
    (lo := (6506157 / 62500000)) (hi := (104098513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69356860583 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69356860583 / 62500000000) = 1/(31250000000 / 69356860583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (199311423 / 250000000) (398622847 / 500000000) (Real.log (69356860583 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (69356860583 / 31250000000) = -Real.log (31250000000 / 69356860583) := by
    rw [show ((69356860583 / 31250000000) : ℝ) = ((31250000000 / 69356860583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (800928213 / 1000000000) ≤ -Real.log (250000000000 / 556901916231) ∧
    -Real.log (250000000000 / 556901916231) ≤ (160185643 / 200000000) := by
  have h := checkLog_sound (w := (56901916231 / 1056901916231)) (n := 12)
    (lo := (107781033 / 1000000000)) (hi := (53890517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556901916231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556901916231 / 500000000000) = 1/(250000000000 / 556901916231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (800928213 / 1000000000) (160185643 / 200000000) (Real.log (556901916231 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (556901916231 / 250000000000) = -Real.log (250000000000 / 556901916231) := by
    rw [show ((556901916231 / 250000000000) : ℝ) = ((250000000000 / 556901916231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0143

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0144Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0144
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

theorem reflection_log_1_neg : (73938717 / 250000000) ≤ -Real.log (2560 / 3441) ∧
    -Real.log (2560 / 3441) ≤ (295754869 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 6001)) (n := 12)
    (lo := (73938717 / 250000000)) (hi := (295754869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3441 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3441 / 2560) = 1/(2560 / 3441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73938717 / 250000000) (295754869 / 1000000000) (Real.log (3441 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3441 / 2560) = -Real.log (2560 / 3441) := by
    rw [show ((3441 / 2560) : ℝ) = ((2560 / 3441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5272611 / 12500000) ≤ -Real.log (1679 / 2560) ∧
    -Real.log (1679 / 2560) ≤ (421808881 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 4239)) (n := 12)
    (lo := (5272611 / 12500000)) (hi := (421808881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1679) = 1/(1679 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-421808881 / 1000000000) (-5272611 / 12500000) (Real.log (1679 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (36860331 / 125000000) ≤ -Real.log (1280 / 1719) ∧
    -Real.log (1280 / 1719) ≤ (294882649 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2999)) (n := 12)
    (lo := (36860331 / 125000000)) (hi := (294882649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1280) = 1/(1280 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (36860331 / 125000000) (294882649 / 1000000000) (Real.log (1719 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1719 / 1280) = -Real.log (1280 / 1719) := by
    rw [show ((1719 / 1280) : ℝ) = ((1280 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26251481 / 62500000) ≤ -Real.log (841 / 1280) ∧
    -Real.log (841 / 1280) ≤ (420023697 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2121)) (n := 12)
    (lo := (26251481 / 62500000)) (hi := (420023697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 841) = 1/(841 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-420023697 / 1000000000) (-26251481 / 62500000) (Real.log (841 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (523710999 / 1000000000) ≤ -Real.log (1280 / 2161) ∧
    -Real.log (1280 / 2161) ≤ (523711 / 1000000) := by
  have h := checkLog_sound (w := (881 / 3441)) (n := 12)
    (lo := (523710999 / 1000000000)) (hi := (523711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2161 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2161 / 1280) = 1/(1280 / 2161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (523710999 / 1000000000) (523711 / 1000000) (Real.log (2161 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2161 / 1280) = -Real.log (1280 / 2161) := by
    rw [show ((2161 / 1280) : ℝ) = ((1280 / 2161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1165653939 / 1000000000) ≤ -Real.log (399 / 1280) ∧
    -Real.log (399 / 1280) ≤ (1165653941 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 399) = 1/(399 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1165653941 / 1000000000) (-1165653939 / 1000000000) (Real.log (399 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (130580447 / 250000000) ≤ -Real.log (640 / 1079) ∧
    -Real.log (640 / 1079) ≤ (522321789 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1719)) (n := 12)
    (lo := (130580447 / 250000000)) (hi := (522321789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079 / 640) = 1/(640 / 1079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (130580447 / 250000000) (522321789 / 1000000000) (Real.log (1079 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1079 / 640) = -Real.log (640 / 1079) := by
    rw [show ((1079 / 640) : ℝ) = ((640 / 1079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1158163267 / 1000000000) ≤ -Real.log (201 / 640) ∧
    -Real.log (201 / 640) ≤ (1158163269 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 201) = 1/(201 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1158163269 / 1000000000) (-1158163267 / 1000000000) (Real.log (201 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (100879971 / 250000000) ≤ -Real.log (200000 / 299417) ∧
    -Real.log (200000 / 299417) ≤ (80703977 / 200000000) := by
  have h := checkLog_sound (w := (99417 / 499417)) (n := 12)
    (lo := (100879971 / 250000000)) (hi := (80703977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299417 / 200000) = 1/(200000 / 299417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (100879971 / 250000000) (80703977 / 200000000) (Real.log (299417 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299417 / 200000) = -Real.log (200000 / 299417) := by
    rw [show ((299417 / 200000) : ℝ) = ((200000 / 299417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (687334109 / 1000000000) ≤ -Real.log (100583 / 200000) ∧
    -Real.log (100583 / 200000) ≤ (68733411 / 100000000) := by
  have h := checkLog_sound (w := (99417 / 300583)) (n := 12)
    (lo := (687334109 / 1000000000)) (hi := (68733411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 100583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 100583) = 1/(100583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68733411 / 100000000) (-687334109 / 1000000000) (Real.log (100583 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50590771 / 125000000) ≤ -Real.log (250000 / 374723) ∧
    -Real.log (250000 / 374723) ≤ (404726169 / 1000000000) := by
  have h := checkLog_sound (w := (124723 / 624723)) (n := 12)
    (lo := (50590771 / 125000000)) (hi := (404726169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374723 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374723 / 250000) = 1/(250000 / 374723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50590771 / 125000000) (404726169 / 1000000000) (Real.log (374723 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374723 / 250000) = -Real.log (250000 / 374723) := by
    rw [show ((374723 / 250000) : ℝ) = ((250000 / 374723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5397919 / 7812500) ≤ -Real.log (125277 / 250000) ∧
    -Real.log (125277 / 250000) ≤ (690933633 / 1000000000) := by
  have h := checkLog_sound (w := (124723 / 375277)) (n := 12)
    (lo := (5397919 / 7812500)) (hi := (690933633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 125277) = 1/(125277 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-690933633 / 1000000000) (-5397919 / 7812500) (Real.log (125277 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (80013113 / 250000000) ≤ -Real.log (2500 / 3443) ∧
    -Real.log (2500 / 3443) ≤ (320052453 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5943)) (n := 12)
    (lo := (80013113 / 250000000)) (hi := (320052453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3443 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3443 / 2500) = 1/(2500 / 3443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (80013113 / 250000000) (320052453 / 1000000000) (Real.log (3443 / 2500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3443 / 2500) = -Real.log (2500 / 3443) := by
    rw [show ((3443 / 2500) : ℝ) = ((2500 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (473529839 / 1000000000) ≤ -Real.log (1557 / 2500) ∧
    -Real.log (1557 / 2500) ≤ (5919123 / 12500000) := by
  have h := checkLog_sound (w := (943 / 4057)) (n := 12)
    (lo := (473529839 / 1000000000)) (hi := (5919123 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1557) = 1/(1557 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5919123 / 12500000) (-473529839 / 1000000000) (Real.log (1557 / 2500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160596261 / 500000000) ≤ -Real.log (1000000 / 1378771) ∧
    -Real.log (1000000 / 1378771) ≤ (321192523 / 1000000000) := by
  have h := checkLog_sound (w := (378771 / 2378771)) (n := 12)
    (lo := (160596261 / 500000000)) (hi := (321192523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378771 / 1000000) = 1/(1000000 / 1378771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160596261 / 500000000) (321192523 / 1000000000) (Real.log (1378771 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1378771 / 1000000) = -Real.log (1000000 / 1378771) := by
    rw [show ((1378771 / 1000000) : ℝ) = ((1000000 / 1378771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (29753469 / 62500000) ≤ -Real.log (621229 / 1000000) ∧
    -Real.log (621229 / 1000000) ≤ (95211101 / 200000000) := by
  have h := checkLog_sound (w := (378771 / 1621229)) (n := 12)
    (lo := (29753469 / 62500000)) (hi := (95211101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621229) = 1/(621229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-95211101 / 200000000) (-29753469 / 62500000) (Real.log (621229 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (136356749 / 125000000) ≤ -Real.log (250000000000 / 744203791893) ∧
    -Real.log (250000000000 / 744203791893) ≤ (545426997 / 500000000) := by
  have h := checkLog_sound (w := (244203791893 / 1244203791893)) (n := 12)
    (lo := (99426703 / 250000000)) (hi := (397706813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744203791893 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(744203791893 / 500000000000) = 1/(250000000000 / 744203791893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (136356749 / 125000000) (545426997 / 500000000) (Real.log (744203791893 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (744203791893 / 250000000000) = -Real.log (250000000000 / 744203791893) := by
    rw [show ((744203791893 / 250000000000) : ℝ) = ((250000000000 / 744203791893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5478299 / 5000000) ≤ -Real.log (500000000000 / 1495577799597) ∧
    -Real.log (500000000000 / 1495577799597) ≤ (547829901 / 500000000) := by
  have h := checkLog_sound (w := (495577799597 / 2495577799597)) (n := 12)
    (lo := (20125631 / 50000000)) (hi := (402512621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495577799597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495577799597 / 1000000000000) = 1/(500000000000 / 1495577799597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5478299 / 5000000) (547829901 / 500000000) (Real.log (1495577799597 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1495577799597 / 500000000000) = -Real.log (500000000000 / 1495577799597) := by
    rw [show ((1495577799597 / 500000000000) : ℝ) = ((500000000000 / 1495577799597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (79358229 / 100000000) ≤ -Real.log (500000000000 / 1105651894669) ∧
    -Real.log (500000000000 / 1105651894669) ≤ (198395573 / 250000000) := by
  have h := checkLog_sound (w := (105651894669 / 2105651894669)) (n := 12)
    (lo := (10043511 / 100000000)) (hi := (100435111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105651894669 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1105651894669 / 1000000000000) = 1/(500000000000 / 1105651894669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (79358229 / 100000000) (198395573 / 250000000) (Real.log (1105651894669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1105651894669 / 500000000000) = -Real.log (500000000000 / 1105651894669) := by
    rw [show ((1105651894669 / 500000000000) : ℝ) = ((500000000000 / 1105651894669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (797248027 / 1000000000) ≤ -Real.log (500000000000 / 1109712360499) ∧
    -Real.log (500000000000 / 1109712360499) ≤ (797248029 / 1000000000) := by
  have h := checkLog_sound (w := (109712360499 / 2109712360499)) (n := 12)
    (lo := (104100847 / 1000000000)) (hi := (6506303 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109712360499 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1109712360499 / 1000000000000) = 1/(500000000000 / 1109712360499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (797248027 / 1000000000) (797248029 / 1000000000) (Real.log (1109712360499 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1109712360499 / 500000000000) = -Real.log (500000000000 / 1109712360499) := by
    rw [show ((1109712360499 / 500000000000) : ℝ) = ((500000000000 / 1109712360499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0144

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0145Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0145
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

theorem reflection_log_1_neg : (36860331 / 125000000) ≤ -Real.log (1280 / 1719) ∧
    -Real.log (1280 / 1719) ≤ (294882649 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2999)) (n := 12)
    (lo := (36860331 / 125000000)) (hi := (294882649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1280) = 1/(1280 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (36860331 / 125000000) (294882649 / 1000000000) (Real.log (1719 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1719 / 1280) = -Real.log (1280 / 1719) := by
    rw [show ((1719 / 1280) : ℝ) = ((1280 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26251481 / 62500000) ≤ -Real.log (841 / 1280) ∧
    -Real.log (841 / 1280) ≤ (420023697 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2121)) (n := 12)
    (lo := (26251481 / 62500000)) (hi := (420023697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 841) = 1/(841 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-420023697 / 1000000000) (-26251481 / 62500000) (Real.log (841 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (294009667 / 1000000000) ≤ -Real.log (512 / 687) ∧
    -Real.log (512 / 687) ≤ (73502417 / 250000000) := by
  have h := checkLog_sound (w := (175 / 1199)) (n := 12)
    (lo := (294009667 / 1000000000)) (hi := (73502417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 512) = 1/(512 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (294009667 / 1000000000) (73502417 / 250000000) (Real.log (687 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (687 / 512) = -Real.log (512 / 687) := by
    rw [show ((687 / 512) : ℝ) = ((512 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (209120847 / 500000000) ≤ -Real.log (337 / 512) ∧
    -Real.log (337 / 512) ≤ (83648339 / 200000000) := by
  have h := checkLog_sound (w := (175 / 849)) (n := 12)
    (lo := (209120847 / 500000000)) (hi := (83648339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 337) = 1/(337 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83648339 / 200000000) (-209120847 / 500000000) (Real.log (337 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (130580447 / 250000000) ≤ -Real.log (640 / 1079) ∧
    -Real.log (640 / 1079) ≤ (522321789 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1719)) (n := 12)
    (lo := (130580447 / 250000000)) (hi := (522321789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079 / 640) = 1/(640 / 1079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (130580447 / 250000000) (522321789 / 1000000000) (Real.log (1079 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1079 / 640) = -Real.log (640 / 1079) := by
    rw [show ((1079 / 640) : ℝ) = ((640 / 1079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1158163267 / 1000000000) ≤ -Real.log (201 / 640) ∧
    -Real.log (201 / 640) ≤ (1158163269 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 201) = 1/(201 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1158163269 / 1000000000) (-1158163267 / 1000000000) (Real.log (201 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (104186129 / 200000000) ≤ -Real.log (256 / 431) ∧
    -Real.log (256 / 431) ≤ (260465323 / 500000000) := by
  have h := checkLog_sound (w := (175 / 687)) (n := 12)
    (lo := (104186129 / 200000000)) (hi := (260465323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431 / 256) = 1/(256 / 431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (104186129 / 200000000) (260465323 / 500000000) (Real.log (431 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (431 / 256) = -Real.log (256 / 431) := by
    rw [show ((431 / 256) : ℝ) = ((256 / 431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1150728289 / 1000000000) ≤ -Real.log (81 / 256) ∧
    -Real.log (81 / 256) ≤ (1150728291 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 81) = 1/(81 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1150728291 / 1000000000) (-1150728289 / 1000000000) (Real.log (81 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10057837 / 25000000) ≤ -Real.log (12500 / 18691) ∧
    -Real.log (12500 / 18691) ≤ (402313481 / 1000000000) := by
  have h := checkLog_sound (w := (6191 / 31191)) (n := 12)
    (lo := (10057837 / 25000000)) (hi := (402313481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18691 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18691 / 12500) = 1/(12500 / 18691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10057837 / 25000000) (402313481 / 1000000000) (Real.log (18691 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18691 / 12500) = -Real.log (12500 / 18691) := by
    rw [show ((18691 / 12500) : ℝ) = ((12500 / 18691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (341875729 / 500000000) ≤ -Real.log (6309 / 12500) ∧
    -Real.log (6309 / 12500) ≤ (683751459 / 1000000000) := by
  have h := checkLog_sound (w := (6191 / 18809)) (n := 12)
    (lo := (341875729 / 500000000)) (hi := (683751459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 6309) = 1/(6309 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-683751459 / 1000000000) (-341875729 / 500000000) (Real.log (6309 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50440069 / 125000000) ≤ -Real.log (500000 / 748543) ∧
    -Real.log (500000 / 748543) ≤ (403520553 / 1000000000) := by
  have h := checkLog_sound (w := (248543 / 1248543)) (n := 12)
    (lo := (50440069 / 125000000)) (hi := (403520553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748543 / 500000) = 1/(500000 / 748543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50440069 / 125000000) (403520553 / 1000000000) (Real.log (748543 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (748543 / 500000) = -Real.log (500000 / 748543) := by
    rw [show ((748543 / 500000) : ℝ) = ((500000 / 748543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (687336097 / 1000000000) ≤ -Real.log (251457 / 500000) ∧
    -Real.log (251457 / 500000) ≤ (343668049 / 500000000) := by
  have h := checkLog_sound (w := (248543 / 751457)) (n := 12)
    (lo := (687336097 / 1000000000)) (hi := (343668049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 251457) = 1/(251457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-343668049 / 500000000) (-687336097 / 1000000000) (Real.log (251457 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (79728497 / 250000000) ≤ -Real.log (1000000 / 1375633) ∧
    -Real.log (1000000 / 1375633) ≤ (318913989 / 1000000000) := by
  have h := checkLog_sound (w := (375633 / 2375633)) (n := 12)
    (lo := (79728497 / 250000000)) (hi := (318913989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1375633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1375633 / 1000000) = 1/(1000000 / 1375633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (79728497 / 250000000) (318913989 / 1000000000) (Real.log (1375633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1375633 / 1000000) = -Real.log (1000000 / 1375633) := by
    rw [show ((1375633 / 1000000) : ℝ) = ((1000000 / 1375633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (235508471 / 500000000) ≤ -Real.log (624367 / 1000000) ∧
    -Real.log (624367 / 1000000) ≤ (471016943 / 1000000000) := by
  have h := checkLog_sound (w := (375633 / 1624367)) (n := 12)
    (lo := (235508471 / 500000000)) (hi := (471016943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 624367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 624367) = 1/(624367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-471016943 / 1000000000) (-235508471 / 500000000) (Real.log (624367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160026589 / 500000000) ≤ -Real.log (1000000 / 1377201) ∧
    -Real.log (1000000 / 1377201) ≤ (320053179 / 1000000000) := by
  have h := checkLog_sound (w := (377201 / 2377201)) (n := 12)
    (lo := (160026589 / 500000000)) (hi := (320053179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377201 / 1000000) = 1/(1000000 / 1377201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160026589 / 500000000) (320053179 / 1000000000) (Real.log (1377201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1377201 / 1000000) = -Real.log (1000000 / 1377201) := by
    rw [show ((1377201 / 1000000) : ℝ) = ((1000000 / 1377201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118382861 / 250000000) ≤ -Real.log (622799 / 1000000) ∧
    -Real.log (622799 / 1000000) ≤ (94706289 / 200000000) := by
  have h := checkLog_sound (w := (377201 / 1622799)) (n := 12)
    (lo := (118382861 / 250000000)) (hi := (94706289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 622799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 622799) = 1/(622799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-94706289 / 200000000) (-118382861 / 250000000) (Real.log (622799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (543032469 / 500000000) ≤ -Real.log (500000000000 / 1481296560469) ∧
    -Real.log (500000000000 / 1481296560469) ≤ (54303247 / 50000000) := by
  have h := checkLog_sound (w := (481296560469 / 2481296560469)) (n := 12)
    (lo := (196458879 / 500000000)) (hi := (392917759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481296560469 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1481296560469 / 1000000000000) = 1/(500000000000 / 1481296560469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (543032469 / 500000000) (54303247 / 50000000) (Real.log (1481296560469 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1481296560469 / 500000000000) = -Real.log (500000000000 / 1481296560469) := by
    rw [show ((1481296560469 / 500000000000) : ℝ) = ((500000000000 / 1481296560469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1090856649 / 1000000000) ≤ -Real.log (12500000000 / 37210288439) ∧
    -Real.log (12500000000 / 37210288439) ≤ (1090856651 / 1000000000) := by
  have h := checkLog_sound (w := (12210288439 / 62210288439)) (n := 12)
    (lo := (397709469 / 1000000000)) (hi := (39770947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37210288439 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37210288439 / 25000000000) = 1/(12500000000 / 37210288439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1090856649 / 1000000000) (1090856651 / 1000000000) (Real.log (37210288439 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37210288439 / 12500000000) = -Real.log (12500000000 / 37210288439) := by
    rw [show ((37210288439 / 12500000000) : ℝ) = ((12500000000 / 37210288439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (78993093 / 100000000) ≤ -Real.log (250000000000 / 550811061443) ∧
    -Real.log (250000000000 / 550811061443) ≤ (197482733 / 250000000) := by
  have h := checkLog_sound (w := (50811061443 / 1050811061443)) (n := 12)
    (lo := (77427 / 800000)) (hi := (96783751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550811061443 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(550811061443 / 500000000000) = 1/(250000000000 / 550811061443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (78993093 / 100000000) (197482733 / 250000000) (Real.log (550811061443 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (550811061443 / 250000000000) = -Real.log (250000000000 / 550811061443) := by
    rw [show ((550811061443 / 250000000000) : ℝ) = ((250000000000 / 550811061443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (396792311 / 500000000) ≤ -Real.log (62500000000 / 138206809099) ∧
    -Real.log (62500000000 / 138206809099) ≤ (49599039 / 62500000) := by
  have h := checkLog_sound (w := (13206809099 / 263206809099)) (n := 12)
    (lo := (50218721 / 500000000)) (hi := (100437443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138206809099 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138206809099 / 125000000000) = 1/(62500000000 / 138206809099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (396792311 / 500000000) (49599039 / 62500000) (Real.log (138206809099 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (138206809099 / 62500000000) = -Real.log (62500000000 / 138206809099) := by
    rw [show ((138206809099 / 62500000000) : ℝ) = ((62500000000 / 138206809099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0145

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0146Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0146
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

theorem reflection_log_1_neg : (294009667 / 1000000000) ≤ -Real.log (512 / 687) ∧
    -Real.log (512 / 687) ≤ (73502417 / 250000000) := by
  have h := checkLog_sound (w := (175 / 1199)) (n := 12)
    (lo := (294009667 / 1000000000)) (hi := (73502417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 512) = 1/(512 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (294009667 / 1000000000) (73502417 / 250000000) (Real.log (687 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (687 / 512) = -Real.log (512 / 687) := by
    rw [show ((687 / 512) : ℝ) = ((512 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (209120847 / 500000000) ≤ -Real.log (337 / 512) ∧
    -Real.log (337 / 512) ≤ (83648339 / 200000000) := by
  have h := checkLog_sound (w := (175 / 849)) (n := 12)
    (lo := (209120847 / 500000000)) (hi := (83648339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 337) = 1/(337 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83648339 / 200000000) (-209120847 / 500000000) (Real.log (337 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (293135923 / 1000000000) ≤ -Real.log (320 / 429) ∧
    -Real.log (320 / 429) ≤ (73283981 / 250000000) := by
  have h := checkLog_sound (w := (109 / 749)) (n := 12)
    (lo := (293135923 / 1000000000)) (hi := (73283981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 320) = 1/(320 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (293135923 / 1000000000) (73283981 / 250000000) (Real.log (429 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (429 / 320) = -Real.log (320 / 429) := by
    rw [show ((429 / 320) : ℝ) = ((320 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208231431 / 500000000) ≤ -Real.log (211 / 320) ∧
    -Real.log (211 / 320) ≤ (416462863 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 531)) (n := 12)
    (lo := (208231431 / 500000000)) (hi := (416462863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 211) = 1/(211 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-416462863 / 1000000000) (-208231431 / 500000000) (Real.log (211 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (104186129 / 200000000) ≤ -Real.log (256 / 431) ∧
    -Real.log (256 / 431) ≤ (260465323 / 500000000) := by
  have h := checkLog_sound (w := (175 / 687)) (n := 12)
    (lo := (104186129 / 200000000)) (hi := (260465323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431 / 256) = 1/(256 / 431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (104186129 / 200000000) (260465323 / 500000000) (Real.log (431 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (431 / 256) = -Real.log (256 / 431) := by
    rw [show ((431 / 256) : ℝ) = ((256 / 431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1150728289 / 1000000000) ≤ -Real.log (81 / 256) ∧
    -Real.log (81 / 256) ≤ (1150728291 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 81) = 1/(81 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1150728291 / 1000000000) (-1150728289 / 1000000000) (Real.log (81 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (129884391 / 250000000) ≤ -Real.log (160 / 269) ∧
    -Real.log (160 / 269) ≤ (103907513 / 200000000) := by
  have h := checkLog_sound (w := (109 / 429)) (n := 12)
    (lo := (129884391 / 250000000)) (hi := (103907513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269 / 160) = 1/(160 / 269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (129884391 / 250000000) (103907513 / 200000000) (Real.log (269 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (269 / 160) = -Real.log (160 / 269) := by
    rw [show ((269 / 160) : ℝ) = ((160 / 269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1143348181 / 1000000000) ≤ -Real.log (51 / 160) ∧
    -Real.log (51 / 160) ≤ (1143348183 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 51) = 1/(51 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1143348183 / 1000000000) (-1143348181 / 1000000000) (Real.log (51 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (200553479 / 500000000) ≤ -Real.log (1000000 / 1493477) ∧
    -Real.log (1000000 / 1493477) ≤ (401106959 / 1000000000) := by
  have h := checkLog_sound (w := (493477 / 2493477)) (n := 12)
    (lo := (200553479 / 500000000)) (hi := (401106959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493477 / 1000000) = 1/(1000000 / 1493477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (200553479 / 500000000) (401106959 / 1000000000) (Real.log (1493477 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1493477 / 1000000) = -Real.log (1000000 / 1493477) := by
    rw [show ((1493477 / 1000000) : ℝ) = ((1000000 / 1493477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (340092773 / 500000000) ≤ -Real.log (506523 / 1000000) ∧
    -Real.log (506523 / 1000000) ≤ (680185547 / 1000000000) := by
  have h := checkLog_sound (w := (493477 / 1506523)) (n := 12)
    (lo := (340092773 / 500000000)) (hi := (680185547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 506523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 506523) = 1/(506523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-680185547 / 1000000000) (-340092773 / 500000000) (Real.log (506523 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (402314149 / 1000000000) ≤ -Real.log (1000000 / 1495281) ∧
    -Real.log (1000000 / 1495281) ≤ (8046283 / 20000000) := by
  have h := checkLog_sound (w := (495281 / 2495281)) (n := 12)
    (lo := (402314149 / 1000000000)) (hi := (8046283 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1495281 / 1000000) = 1/(1000000 / 1495281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (402314149 / 1000000000) (8046283 / 20000000) (Real.log (1495281 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1495281 / 1000000) = -Real.log (1000000 / 1495281) := by
    rw [show ((1495281 / 1000000) : ℝ) = ((1000000 / 1495281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4273459 / 6250000) ≤ -Real.log (504719 / 1000000) ∧
    -Real.log (504719 / 1000000) ≤ (683753441 / 1000000000) := by
  have h := checkLog_sound (w := (495281 / 1504719)) (n := 12)
    (lo := (4273459 / 6250000)) (hi := (683753441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 504719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 504719) = 1/(504719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-683753441 / 1000000000) (-4273459 / 6250000) (Real.log (504719 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (31777641 / 100000000) ≤ -Real.log (1000000 / 1374069) ∧
    -Real.log (1000000 / 1374069) ≤ (317776411 / 1000000000) := by
  have h := checkLog_sound (w := (374069 / 2374069)) (n := 12)
    (lo := (31777641 / 100000000)) (hi := (317776411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374069 / 1000000) = 1/(1000000 / 1374069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (31777641 / 100000000) (317776411 / 1000000000) (Real.log (1374069 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1374069 / 1000000) = -Real.log (1000000 / 1374069) := by
    rw [show ((1374069 / 1000000) : ℝ) = ((1000000 / 1374069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (468515137 / 1000000000) ≤ -Real.log (625931 / 1000000) ∧
    -Real.log (625931 / 1000000) ≤ (234257569 / 500000000) := by
  have h := checkLog_sound (w := (374069 / 1625931)) (n := 12)
    (lo := (468515137 / 1000000000)) (hi := (234257569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625931) = 1/(625931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-234257569 / 500000000) (-468515137 / 1000000000) (Real.log (625931 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63782943 / 200000000) ≤ -Real.log (500000 / 687817) ∧
    -Real.log (500000 / 687817) ≤ (79728679 / 250000000) := by
  have h := checkLog_sound (w := (187817 / 1187817)) (n := 12)
    (lo := (63782943 / 200000000)) (hi := (79728679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687817 / 500000) = 1/(500000 / 687817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63782943 / 200000000) (79728679 / 250000000) (Real.log (687817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (687817 / 500000) = -Real.log (500000 / 687817) := by
    rw [show ((687817 / 500000) : ℝ) = ((500000 / 687817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (29438659 / 62500000) ≤ -Real.log (312183 / 500000) ∧
    -Real.log (312183 / 500000) ≤ (94203709 / 200000000) := by
  have h := checkLog_sound (w := (187817 / 812183)) (n := 12)
    (lo := (29438659 / 62500000)) (hi := (94203709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 312183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 312183) = 1/(312183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-94203709 / 200000000) (-29438659 / 62500000) (Real.log (312183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (135161563 / 125000000) ≤ -Real.log (500000000000 / 1474244012611) ∧
    -Real.log (500000000000 / 1474244012611) ≤ (540646253 / 500000000) := by
  have h := checkLog_sound (w := (474244012611 / 2474244012611)) (n := 12)
    (lo := (97036331 / 250000000)) (hi := (15525813 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474244012611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1474244012611 / 1000000000000) = 1/(500000000000 / 1474244012611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (135161563 / 125000000) (540646253 / 500000000) (Real.log (1474244012611 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1474244012611 / 500000000000) = -Real.log (500000000000 / 1474244012611) := by
    rw [show ((1474244012611 / 500000000000) : ℝ) = ((500000000000 / 1474244012611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (271516897 / 250000000) ≤ -Real.log (250000000000 / 740650243007) ∧
    -Real.log (250000000000 / 740650243007) ≤ (108606759 / 100000000) := by
  have h := checkLog_sound (w := (240650243007 / 1240650243007)) (n := 12)
    (lo := (49115051 / 125000000)) (hi := (392920409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740650243007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(740650243007 / 500000000000) = 1/(250000000000 / 740650243007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (271516897 / 250000000) (108606759 / 100000000) (Real.log (740650243007 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (740650243007 / 250000000000) = -Real.log (250000000000 / 740650243007) := by
    rw [show ((740650243007 / 250000000000) : ℝ) = ((250000000000 / 740650243007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (786291547 / 1000000000) ≤ -Real.log (125000000000 / 274405046243) ∧
    -Real.log (125000000000 / 274405046243) ≤ (786291549 / 1000000000) := by
  have h := checkLog_sound (w := (24405046243 / 524405046243)) (n := 12)
    (lo := (93144367 / 1000000000)) (hi := (5821523 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274405046243 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(274405046243 / 250000000000) = 1/(125000000000 / 274405046243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (786291547 / 1000000000) (786291549 / 1000000000) (Real.log (274405046243 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (274405046243 / 125000000000) = -Real.log (125000000000 / 274405046243) := by
    rw [show ((274405046243 / 125000000000) : ℝ) = ((125000000000 / 274405046243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (789933259 / 1000000000) ≤ -Real.log (125000000000 / 275406172021) ∧
    -Real.log (125000000000 / 275406172021) ≤ (789933261 / 1000000000) := by
  have h := checkLog_sound (w := (25406172021 / 525406172021)) (n := 12)
    (lo := (96786079 / 1000000000)) (hi := (604913 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275406172021 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275406172021 / 250000000000) = 1/(125000000000 / 275406172021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (789933259 / 1000000000) (789933261 / 1000000000) (Real.log (275406172021 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (275406172021 / 125000000000) = -Real.log (125000000000 / 275406172021) := by
    rw [show ((275406172021 / 125000000000) : ℝ) = ((125000000000 / 275406172021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0146

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0147Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0147
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

theorem reflection_log_1_neg : (293135923 / 1000000000) ≤ -Real.log (320 / 429) ∧
    -Real.log (320 / 429) ≤ (73283981 / 250000000) := by
  have h := checkLog_sound (w := (109 / 749)) (n := 12)
    (lo := (293135923 / 1000000000)) (hi := (73283981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 320) = 1/(320 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (293135923 / 1000000000) (73283981 / 250000000) (Real.log (429 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (429 / 320) = -Real.log (320 / 429) := by
    rw [show ((429 / 320) : ℝ) = ((320 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208231431 / 500000000) ≤ -Real.log (211 / 320) ∧
    -Real.log (211 / 320) ≤ (416462863 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 531)) (n := 12)
    (lo := (208231431 / 500000000)) (hi := (416462863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 211) = 1/(211 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-416462863 / 1000000000) (-208231431 / 500000000) (Real.log (211 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (146130707 / 500000000) ≤ -Real.log (2560 / 3429) ∧
    -Real.log (2560 / 3429) ≤ (58452283 / 200000000) := by
  have h := checkLog_sound (w := (869 / 5989)) (n := 12)
    (lo := (146130707 / 500000000)) (hi := (58452283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3429 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3429 / 2560) = 1/(2560 / 3429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (146130707 / 500000000) (58452283 / 200000000) (Real.log (3429 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3429 / 2560) = -Real.log (2560 / 3429) := by
    rw [show ((3429 / 2560) : ℝ) = ((2560 / 3429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (103671797 / 250000000) ≤ -Real.log (1691 / 2560) ∧
    -Real.log (1691 / 2560) ≤ (414687189 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 4251)) (n := 12)
    (lo := (103671797 / 250000000)) (hi := (414687189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1691) = 1/(1691 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-414687189 / 1000000000) (-103671797 / 250000000) (Real.log (1691 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (129884391 / 250000000) ≤ -Real.log (160 / 269) ∧
    -Real.log (160 / 269) ≤ (103907513 / 200000000) := by
  have h := checkLog_sound (w := (109 / 429)) (n := 12)
    (lo := (129884391 / 250000000)) (hi := (103907513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269 / 160) = 1/(160 / 269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (129884391 / 250000000) (103907513 / 200000000) (Real.log (269 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (269 / 160) = -Real.log (160 / 269) := by
    rw [show ((269 / 160) : ℝ) = ((160 / 269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1143348181 / 1000000000) ≤ -Real.log (51 / 160) ∧
    -Real.log (51 / 160) ≤ (1143348183 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 51) = 1/(51 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1143348183 / 1000000000) (-1143348181 / 1000000000) (Real.log (51 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (518142539 / 1000000000) ≤ -Real.log (1280 / 2149) ∧
    -Real.log (1280 / 2149) ≤ (25907127 / 50000000) := by
  have h := checkLog_sound (w := (869 / 3429)) (n := 12)
    (lo := (518142539 / 1000000000)) (hi := (25907127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2149 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2149 / 1280) = 1/(1280 / 2149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (518142539 / 1000000000) (25907127 / 50000000) (Real.log (2149 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2149 / 1280) = -Real.log (1280 / 2149) := by
    rw [show ((2149 / 1280) : ℝ) = ((1280 / 2149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1136022141 / 1000000000) ≤ -Real.log (411 / 1280) ∧
    -Real.log (411 / 1280) ≤ (1136022143 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 411) = 1/(411 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1136022143 / 1000000000) (-1136022141 / 1000000000) (Real.log (411 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2499377 / 6250000) ≤ -Real.log (250000 / 372919) ∧
    -Real.log (250000 / 372919) ≤ (399900321 / 1000000000) := by
  have h := checkLog_sound (w := (122919 / 622919)) (n := 12)
    (lo := (2499377 / 6250000)) (hi := (399900321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372919 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372919 / 250000) = 1/(250000 / 372919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2499377 / 6250000) (399900321 / 1000000000) (Real.log (372919 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (372919 / 250000) = -Real.log (250000 / 372919) := by
    rw [show ((372919 / 250000) : ℝ) = ((250000 / 372919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (676636239 / 1000000000) ≤ -Real.log (127081 / 250000) ∧
    -Real.log (127081 / 250000) ≤ (8457953 / 12500000) := by
  have h := checkLog_sound (w := (122919 / 377081)) (n := 12)
    (lo := (676636239 / 1000000000)) (hi := (8457953 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127081) = 1/(127081 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8457953 / 12500000) (-676636239 / 1000000000) (Real.log (127081 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (100276907 / 250000000) ≤ -Real.log (500000 / 746739) ∧
    -Real.log (500000 / 746739) ≤ (401107629 / 1000000000) := by
  have h := checkLog_sound (w := (246739 / 1246739)) (n := 12)
    (lo := (100276907 / 250000000)) (hi := (401107629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746739 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746739 / 500000) = 1/(500000 / 746739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (100276907 / 250000000) (401107629 / 1000000000) (Real.log (746739 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (746739 / 500000) = -Real.log (500000 / 746739) := by
    rw [show ((746739 / 500000) : ℝ) = ((500000 / 746739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1062793 / 1562500) ≤ -Real.log (253261 / 500000) ∧
    -Real.log (253261 / 500000) ≤ (680187521 / 1000000000) := by
  have h := checkLog_sound (w := (246739 / 753261)) (n := 12)
    (lo := (1062793 / 1562500)) (hi := (680187521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 253261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 253261) = 1/(253261 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-680187521 / 1000000000) (-1062793 / 1562500) (Real.log (253261 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15832059 / 50000000) ≤ -Real.log (100000 / 137251) ∧
    -Real.log (100000 / 137251) ≤ (316641181 / 1000000000) := by
  have h := checkLog_sound (w := (37251 / 237251)) (n := 12)
    (lo := (15832059 / 50000000)) (hi := (316641181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137251 / 100000) = 1/(100000 / 137251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15832059 / 50000000) (316641181 / 1000000000) (Real.log (137251 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (137251 / 100000) = -Real.log (100000 / 137251) := by
    rw [show ((137251 / 100000) : ℝ) = ((100000 / 137251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58253443 / 125000000) ≤ -Real.log (62749 / 100000) ∧
    -Real.log (62749 / 100000) ≤ (93205509 / 200000000) := by
  have h := checkLog_sound (w := (37251 / 162749)) (n := 12)
    (lo := (58253443 / 125000000)) (hi := (93205509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62749) = 1/(62749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-93205509 / 200000000) (-58253443 / 125000000) (Real.log (62749 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158888569 / 500000000) ≤ -Real.log (100000 / 137407) ∧
    -Real.log (100000 / 137407) ≤ (317777139 / 1000000000) := by
  have h := checkLog_sound (w := (37407 / 237407)) (n := 12)
    (lo := (158888569 / 500000000)) (hi := (317777139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137407 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137407 / 100000) = 1/(100000 / 137407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158888569 / 500000000) (317777139 / 1000000000) (Real.log (137407 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (137407 / 100000) = -Real.log (100000 / 137407) := by
    rw [show ((137407 / 100000) : ℝ) = ((100000 / 137407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (93703347 / 200000000) ≤ -Real.log (62593 / 100000) ∧
    -Real.log (62593 / 100000) ≤ (3660287 / 7812500) := by
  have h := checkLog_sound (w := (37407 / 162593)) (n := 12)
    (lo := (93703347 / 200000000)) (hi := (3660287 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62593) = 1/(62593 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3660287 / 7812500) (-93703347 / 200000000) (Real.log (62593 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (538268279 / 500000000) ≤ -Real.log (25000000000 / 73362461737) ∧
    -Real.log (25000000000 / 73362461737) ≤ (13456707 / 12500000) := by
  have h := checkLog_sound (w := (23362461737 / 123362461737)) (n := 12)
    (lo := (191694689 / 500000000)) (hi := (383389379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73362461737 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73362461737 / 50000000000) = 1/(25000000000 / 73362461737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (538268279 / 500000000) (13456707 / 12500000) (Real.log (73362461737 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (73362461737 / 25000000000) = -Real.log (25000000000 / 73362461737) := by
    rw [show ((73362461737 / 25000000000) : ℝ) = ((25000000000 / 73362461737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (270323787 / 250000000) ≤ -Real.log (500000000000 / 1474247910259) ∧
    -Real.log (500000000000 / 1474247910259) ≤ (21625903 / 20000000) := by
  have h := checkLog_sound (w := (474247910259 / 2474247910259)) (n := 12)
    (lo := (1516203 / 3906250)) (hi := (388147969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474247910259 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1474247910259 / 1000000000000) = 1/(500000000000 / 1474247910259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (270323787 / 250000000) (21625903 / 20000000) (Real.log (1474247910259 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1474247910259 / 500000000000) = -Real.log (500000000000 / 1474247910259) := by
    rw [show ((1474247910259 / 500000000000) : ℝ) = ((500000000000 / 1474247910259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (195667181 / 250000000) ≤ -Real.log (250000000000 / 546825447417) ∧
    -Real.log (250000000000 / 546825447417) ≤ (391334363 / 500000000) := by
  have h := checkLog_sound (w := (46825447417 / 1046825447417)) (n := 12)
    (lo := (11190193 / 125000000)) (hi := (17904309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546825447417 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(546825447417 / 500000000000) = 1/(250000000000 / 546825447417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (195667181 / 250000000) (391334363 / 500000000) (Real.log (546825447417 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (546825447417 / 250000000000) = -Real.log (250000000000 / 546825447417) := by
    rw [show ((546825447417 / 250000000000) : ℝ) = ((250000000000 / 546825447417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (786293873 / 1000000000) ≤ -Real.log (500000000000 / 1097622737367) ∧
    -Real.log (500000000000 / 1097622737367) ≤ (6290351 / 8000000) := by
  have h := checkLog_sound (w := (97622737367 / 2097622737367)) (n := 12)
    (lo := (93146693 / 1000000000)) (hi := (46573347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097622737367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1097622737367 / 1000000000000) = 1/(500000000000 / 1097622737367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (786293873 / 1000000000) (6290351 / 8000000) (Real.log (1097622737367 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1097622737367 / 500000000000) = -Real.log (500000000000 / 1097622737367) := by
    rw [show ((1097622737367 / 500000000000) : ℝ) = ((500000000000 / 1097622737367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0147

end


