-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0180Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0180Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:49:12.331971+00:00
-- url     : https://prove2.me/theorems/85c617b0-78aa-41ea-acc4-bb911e1a657b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0180Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0181Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0180Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0181Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0182Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0185Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0186Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0180Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0181Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0182Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0185Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0186Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0180Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0181Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0182Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0185Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0186Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0180Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0181Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0182Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0183Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0184Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0185Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0186Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0180Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0180
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

theorem reflection_log_1_neg : (626021983 / 1000000000) ≤ -Real.log (6400 / 11969) ∧
    -Real.log (6400 / 11969) ≤ (19563187 / 31250000) := by
  have h := checkLog_sound (w := (5569 / 18369)) (n := 12)
    (lo := (626021983 / 1000000000)) (hi := (19563187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 6400) = 1/(6400 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (626021983 / 1000000000) (19563187 / 31250000) (Real.log (11969 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11969 / 6400) = -Real.log (6400 / 11969) := by
    rw [show ((11969 / 6400) : ℝ) = ((6400 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2041423473 / 1000000000) ≤ -Real.log (831 / 6400) ∧
    -Real.log (831 / 6400) ≤ (510355869 / 250000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 831) = 1/(831 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-510355869 / 250000000) (-2041423473 / 1000000000) (Real.log (831 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (78054161 / 125000000) ≤ -Real.log (128 / 239) ∧
    -Real.log (128 / 239) ≤ (624433289 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 367)) (n := 12)
    (lo := (78054161 / 125000000)) (hi := (624433289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 128) = 1/(128 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (78054161 / 125000000) (624433289 / 1000000000) (Real.log (239 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (239 / 128) = -Real.log (128 / 239) := by
    rw [show ((239 / 128) : ℝ) = ((128 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1009408459 / 500000000) ≤ -Real.log (17 / 128) ∧
    -Real.log (17 / 128) ≤ (2018816921 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 17) = 1/(17 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2018816921 / 1000000000) (-1009408459 / 500000000) (Real.log (17 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (277032347 / 500000000) ≤ -Real.log (3200 / 5569) ∧
    -Real.log (3200 / 5569) ≤ (110812939 / 200000000) := by
  have h := checkLog_sound (w := (2369 / 8769)) (n := 12)
    (lo := (277032347 / 500000000)) (hi := (110812939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5569 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5569 / 3200) = 1/(3200 / 5569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (277032347 / 500000000) (110812939 / 200000000) (Real.log (5569 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5569 / 3200) = -Real.log (3200 / 5569) := by
    rw [show ((5569 / 3200) : ℝ) = ((3200 / 5569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1348276293 / 1000000000) ≤ -Real.log (831 / 3200) ∧
    -Real.log (831 / 3200) ≤ (269655259 / 200000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 831) = 1/(831 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-269655259 / 200000000) (-1348276293 / 1000000000) (Real.log (831 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (550647117 / 1000000000) ≤ -Real.log (64 / 111) ∧
    -Real.log (64 / 111) ≤ (275323559 / 500000000) := by
  have h := checkLog_sound (w := (47 / 175)) (n := 12)
    (lo := (550647117 / 1000000000)) (hi := (275323559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 64) = 1/(64 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (550647117 / 1000000000) (275323559 / 500000000) (Real.log (111 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (111 / 64) = -Real.log (64 / 111) := by
    rw [show ((111 / 64) : ℝ) = ((64 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (662834869 / 500000000) ≤ -Real.log (17 / 64) ∧
    -Real.log (17 / 64) ≤ (66283487 / 50000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 17) = 1/(17 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-66283487 / 50000000) (-662834869 / 500000000) (Real.log (17 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128560687 / 200000000) ≤ -Real.log (200000 / 380361) ∧
    -Real.log (200000 / 380361) ≤ (160700859 / 250000000) := by
  have h := checkLog_sound (w := (180361 / 580361)) (n := 12)
    (lo := (128560687 / 200000000)) (hi := (160700859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380361 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380361 / 200000) = 1/(200000 / 380361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128560687 / 200000000) (160700859 / 250000000) (Real.log (380361 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (380361 / 200000) = -Real.log (200000 / 380361) := by
    rw [show ((380361 / 200000) : ℝ) = ((200000 / 380361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2320799979 / 1000000000) ≤ -Real.log (19639 / 200000) ∧
    -Real.log (19639 / 200000) ≤ (2320799983 / 1000000000) := by
  have h := checkLog_sound (w := (5361 / 44639)) (n := 12)
    (lo := (241358439 / 1000000000)) (hi := (6033961 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19639) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 19639) = 1/(19639 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2320799983 / 1000000000) (-2320799979 / 1000000000) (Real.log (19639 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (321897579 / 500000000) ≤ -Real.log (250000 / 475923) ∧
    -Real.log (250000 / 475923) ≤ (643795159 / 1000000000) := by
  have h := checkLog_sound (w := (225923 / 725923)) (n := 12)
    (lo := (321897579 / 500000000)) (hi := (643795159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475923 / 250000) = 1/(250000 / 475923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (321897579 / 500000000) (643795159 / 1000000000) (Real.log (475923 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (475923 / 250000) = -Real.log (250000 / 475923) := by
    rw [show ((475923 / 250000) : ℝ) = ((250000 / 475923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146262743 / 62500000) ≤ -Real.log (24077 / 250000) ∧
    -Real.log (24077 / 250000) ≤ (585050973 / 250000000) := by
  have h := checkLog_sound (w := (7173 / 55327)) (n := 12)
    (lo := (65190587 / 250000000)) (hi := (260762349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24077) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 24077) = 1/(24077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-585050973 / 250000000) (-146262743 / 62500000) (Real.log (24077 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25615017 / 40000000) ≤ -Real.log (1000000 / 1897193) ∧
    -Real.log (1000000 / 1897193) ≤ (320187713 / 500000000) := by
  have h := checkLog_sound (w := (897193 / 2897193)) (n := 12)
    (lo := (25615017 / 40000000)) (hi := (320187713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1897193 / 1000000) = 1/(1000000 / 1897193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25615017 / 40000000) (320187713 / 500000000) (Real.log (1897193 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1897193 / 1000000) = -Real.log (1000000 / 1897193) := by
    rw [show ((1897193 / 1000000) : ℝ) = ((1000000 / 1897193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2274901833 / 1000000000) ≤ -Real.log (102807 / 1000000) ∧
    -Real.log (102807 / 1000000) ≤ (2274901837 / 1000000000) := by
  have h := checkLog_sound (w := (22193 / 227807)) (n := 12)
    (lo := (195460293 / 1000000000)) (hi := (97730147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 102807) = 1/(102807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2274901837 / 1000000000) (-2274901833 / 1000000000) (Real.log (102807 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (641496453 / 1000000000) ≤ -Real.log (1000000 / 1899321) ∧
    -Real.log (1000000 / 1899321) ≤ (320748227 / 500000000) := by
  have h := checkLog_sound (w := (899321 / 2899321)) (n := 12)
    (lo := (641496453 / 1000000000)) (hi := (320748227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899321 / 1000000) = 1/(1000000 / 1899321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (641496453 / 1000000000) (320748227 / 500000000) (Real.log (1899321 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1899321 / 1000000) = -Real.log (1000000 / 1899321) := by
    rw [show ((1899321 / 1000000) : ℝ) = ((1000000 / 1899321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2295818039 / 1000000000) ≤ -Real.log (100679 / 1000000) ∧
    -Real.log (100679 / 1000000) ≤ (2295818043 / 1000000000) := by
  have h := checkLog_sound (w := (24321 / 225679)) (n := 12)
    (lo := (216376499 / 1000000000)) (hi := (432753 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100679) = 1/(100679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2295818043 / 1000000000) (-2295818039 / 1000000000) (Real.log (100679 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1481801707 / 500000000) ≤ -Real.log (100000000000 / 1936763582667) ∧
    -Real.log (100000000000 / 1936763582667) ≤ (2963603419 / 1000000000) := by
  have h := checkLog_sound (w := (336763582667 / 3536763582667)) (n := 12)
    (lo := (95507347 / 500000000)) (hi := (38202939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936763582667 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1936763582667 / 1600000000000) = 1/(100000000000 / 1936763582667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1481801707 / 500000000) (2963603419 / 1000000000) (Real.log (1936763582667 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1936763582667 / 100000000000) = -Real.log (100000000000 / 1936763582667) := by
    rw [show ((1936763582667 / 100000000000) : ℝ) = ((100000000000 / 1936763582667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1491999523 / 500000000) ≤ -Real.log (500000000000 / 9883353407817) ∧
    -Real.log (500000000000 / 9883353407817) ≤ (2983999051 / 1000000000) := by
  have h := checkLog_sound (w := (1883353407817 / 17883353407817)) (n := 12)
    (lo := (105705163 / 500000000)) (hi := (211410327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9883353407817 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9883353407817 / 8000000000000) = 1/(500000000000 / 9883353407817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1491999523 / 500000000) (2983999051 / 1000000000) (Real.log (9883353407817 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9883353407817 / 500000000000) = -Real.log (500000000000 / 9883353407817) := by
    rw [show ((9883353407817 / 500000000000) : ℝ) = ((500000000000 / 9883353407817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1457638629 / 500000000) ≤ -Real.log (500000000000 / 9226964117229) ∧
    -Real.log (500000000000 / 9226964117229) ≤ (2915277263 / 1000000000) := by
  have h := checkLog_sound (w := (1226964117229 / 17226964117229)) (n := 12)
    (lo := (71344269 / 500000000)) (hi := (142688539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9226964117229 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9226964117229 / 8000000000000) = 1/(500000000000 / 9226964117229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1457638629 / 500000000) (2915277263 / 1000000000) (Real.log (9226964117229 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9226964117229 / 500000000000) = -Real.log (500000000000 / 9226964117229) := by
    rw [show ((9226964117229 / 500000000000) : ℝ) = ((500000000000 / 9226964117229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (734328623 / 250000000) ≤ -Real.log (100000000000 / 1886511586329) ∧
    -Real.log (100000000000 / 1886511586329) ≤ (2937314497 / 1000000000) := by
  have h := checkLog_sound (w := (286511586329 / 3486511586329)) (n := 12)
    (lo := (41181443 / 250000000)) (hi := (164725773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886511586329 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1886511586329 / 1600000000000) = 1/(100000000000 / 1886511586329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (734328623 / 250000000) (2937314497 / 1000000000) (Real.log (1886511586329 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1886511586329 / 100000000000) = -Real.log (100000000000 / 1886511586329) := by
    rw [show ((1886511586329 / 100000000000) : ℝ) = ((100000000000 / 1886511586329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0180

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0181Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0181
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

theorem reflection_log_1_neg : (78054161 / 125000000) ≤ -Real.log (128 / 239) ∧
    -Real.log (128 / 239) ≤ (624433289 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 367)) (n := 12)
    (lo := (78054161 / 125000000)) (hi := (624433289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 128) = 1/(128 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (78054161 / 125000000) (624433289 / 1000000000) (Real.log (239 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (239 / 128) = -Real.log (128 / 239) := by
    rw [show ((239 / 128) : ℝ) = ((128 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1009408459 / 500000000) ≤ -Real.log (17 / 128) ∧
    -Real.log (17 / 128) ≤ (2018816921 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 17) = 1/(17 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2018816921 / 1000000000) (-1009408459 / 500000000) (Real.log (17 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38927629 / 62500000) ≤ -Real.log (6400 / 11931) ∧
    -Real.log (6400 / 11931) ≤ (124568413 / 200000000) := by
  have h := checkLog_sound (w := (5531 / 18331)) (n := 12)
    (lo := (38927629 / 62500000)) (hi := (124568413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 6400) = 1/(6400 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38927629 / 62500000) (124568413 / 200000000) (Real.log (11931 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11931 / 6400) = -Real.log (6400 / 11931) := by
    rw [show ((11931 / 6400) : ℝ) = ((6400 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (998355071 / 500000000) ≤ -Real.log (869 / 6400) ∧
    -Real.log (869 / 6400) ≤ (399342029 / 200000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 869) = 1/(869 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-399342029 / 200000000) (-998355071 / 500000000) (Real.log (869 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (550647117 / 1000000000) ≤ -Real.log (64 / 111) ∧
    -Real.log (64 / 111) ≤ (275323559 / 500000000) := by
  have h := checkLog_sound (w := (47 / 175)) (n := 12)
    (lo := (550647117 / 1000000000)) (hi := (275323559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 64) = 1/(64 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (550647117 / 1000000000) (275323559 / 500000000) (Real.log (111 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (111 / 64) = -Real.log (64 / 111) := by
    rw [show ((111 / 64) : ℝ) = ((64 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (662834869 / 500000000) ≤ -Real.log (17 / 64) ∧
    -Real.log (17 / 64) ≤ (66283487 / 50000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 17) = 1/(17 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-66283487 / 50000000) (-662834869 / 500000000) (Real.log (17 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (547217821 / 1000000000) ≤ -Real.log (3200 / 5531) ∧
    -Real.log (3200 / 5531) ≤ (273608911 / 500000000) := by
  have h := checkLog_sound (w := (2331 / 8731)) (n := 12)
    (lo := (547217821 / 1000000000)) (hi := (273608911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5531 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5531 / 3200) = 1/(3200 / 5531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (547217821 / 1000000000) (273608911 / 500000000) (Real.log (5531 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5531 / 3200) = -Real.log (3200 / 5531) := by
    rw [show ((5531 / 3200) : ℝ) = ((3200 / 5531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (651781481 / 500000000) ≤ -Real.log (869 / 3200) ∧
    -Real.log (869 / 3200) ≤ (325890741 / 250000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 869) = 1/(869 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-325890741 / 250000000) (-651781481 / 500000000) (Real.log (869 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (641817569 / 1000000000) ≤ -Real.log (1000000 / 1899931) ∧
    -Real.log (1000000 / 1899931) ≤ (64181757 / 100000000) := by
  have h := checkLog_sound (w := (899931 / 2899931)) (n := 12)
    (lo := (641817569 / 1000000000)) (hi := (64181757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899931 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899931 / 1000000) = 1/(1000000 / 1899931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (641817569 / 1000000000) (64181757 / 100000000) (Real.log (1899931 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1899931 / 1000000) = -Real.log (1000000 / 1899931) := by
    rw [show ((1899931 / 1000000) : ℝ) = ((1000000 / 1899931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2301895329 / 1000000000) ≤ -Real.log (100069 / 1000000) ∧
    -Real.log (100069 / 1000000) ≤ (2301895333 / 1000000000) := by
  have h := checkLog_sound (w := (24931 / 225069)) (n := 12)
    (lo := (222453789 / 1000000000)) (hi := (22245379 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100069) = 1/(100069 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2301895333 / 1000000000) (-2301895329 / 1000000000) (Real.log (100069 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (642803961 / 1000000000) ≤ -Real.log (500000 / 950903) ∧
    -Real.log (500000 / 950903) ≤ (321401981 / 500000000) := by
  have h := checkLog_sound (w := (450903 / 1450903)) (n := 12)
    (lo := (642803961 / 1000000000)) (hi := (321401981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950903 / 500000) = 1/(500000 / 950903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (642803961 / 1000000000) (321401981 / 500000000) (Real.log (950903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (950903 / 500000) = -Real.log (500000 / 950903) := by
    rw [show ((950903 / 500000) : ℝ) = ((500000 / 950903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2320810163 / 1000000000) ≤ -Real.log (49097 / 500000) ∧
    -Real.log (49097 / 500000) ≤ (2320810167 / 1000000000) := by
  have h := checkLog_sound (w := (13403 / 111597)) (n := 12)
    (lo := (241368623 / 1000000000)) (hi := (15085539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49097) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 49097) = 1/(49097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2320810167 / 1000000000) (-2320810163 / 1000000000) (Real.log (49097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2497097 / 3906250) ≤ -Real.log (31250 / 59221) ∧
    -Real.log (31250 / 59221) ≤ (639256833 / 1000000000) := by
  have h := checkLog_sound (w := (27971 / 90471)) (n := 12)
    (lo := (2497097 / 3906250)) (hi := (639256833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59221 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59221 / 31250) = 1/(31250 / 59221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2497097 / 3906250) (639256833 / 1000000000) (Real.log (59221 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (59221 / 31250) = -Real.log (31250 / 59221) := by
    rw [show ((59221 / 31250) : ℝ) = ((31250 / 59221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (563620219 / 250000000) ≤ -Real.log (3279 / 31250) ∧
    -Real.log (3279 / 31250) ≤ (28181011 / 12500000) := by
  have h := checkLog_sound (w := (2509 / 28741)) (n := 12)
    (lo := (21879917 / 125000000)) (hi := (175039337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13116) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13116) = 1/(3279 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-28181011 / 12500000) (-563620219 / 250000000) (Real.log (3279 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (40023497 / 62500000) ≤ -Real.log (500000 / 948597) ∧
    -Real.log (500000 / 948597) ≤ (640375953 / 1000000000) := by
  have h := checkLog_sound (w := (448597 / 1448597)) (n := 12)
    (lo := (40023497 / 62500000)) (hi := (640375953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948597 / 500000) = 1/(500000 / 948597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40023497 / 62500000) (640375953 / 1000000000) (Real.log (948597 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (948597 / 500000) = -Real.log (500000 / 948597) := by
    rw [show ((948597 / 500000) : ℝ) = ((500000 / 948597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (56872789 / 25000000) ≤ -Real.log (51403 / 500000) ∧
    -Real.log (51403 / 500000) ≤ (568727891 / 250000000) := by
  have h := checkLog_sound (w := (11097 / 113903)) (n := 12)
    (lo := (9773501 / 50000000)) (hi := (195470021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51403) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 51403) = 1/(51403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-568727891 / 250000000) (-56872789 / 25000000) (Real.log (51403 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1471856449 / 500000000) ≤ -Real.log (500000000000 / 9493104757717) ∧
    -Real.log (500000000000 / 9493104757717) ≤ (2943712903 / 1000000000) := by
  have h := checkLog_sound (w := (1493104757717 / 17493104757717)) (n := 12)
    (lo := (85562089 / 500000000)) (hi := (171124179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9493104757717 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9493104757717 / 8000000000000) = 1/(500000000000 / 9493104757717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1471856449 / 500000000) (2943712903 / 1000000000) (Real.log (9493104757717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9493104757717 / 500000000000) = -Real.log (500000000000 / 9493104757717) := by
    rw [show ((9493104757717 / 500000000000) : ℝ) = ((500000000000 / 9493104757717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (740903531 / 250000000) ≤ -Real.log (25000000000 / 484196081227) ∧
    -Real.log (25000000000 / 484196081227) ≤ (2963614129 / 1000000000) := by
  have h := checkLog_sound (w := (84196081227 / 884196081227)) (n := 12)
    (lo := (47756351 / 250000000)) (hi := (38205081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484196081227 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(484196081227 / 400000000000) = 1/(25000000000 / 484196081227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (740903531 / 250000000) (2963614129 / 1000000000) (Real.log (484196081227 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (484196081227 / 25000000000) = -Real.log (25000000000 / 484196081227) := by
    rw [show ((484196081227 / 25000000000) : ℝ) = ((25000000000 / 484196081227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (723434427 / 250000000) ≤ -Real.log (500000000000 / 9030344617261) ∧
    -Real.log (500000000000 / 9030344617261) ≤ (2893737713 / 1000000000) := by
  have h := checkLog_sound (w := (1030344617261 / 17030344617261)) (n := 12)
    (lo := (30287247 / 250000000)) (hi := (121148989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9030344617261 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9030344617261 / 8000000000000) = 1/(500000000000 / 9030344617261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (723434427 / 250000000) (2893737713 / 1000000000) (Real.log (9030344617261 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9030344617261 / 500000000000) = -Real.log (500000000000 / 9030344617261) := by
    rw [show ((9030344617261 / 500000000000) : ℝ) = ((500000000000 / 9030344617261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (364410939 / 125000000) ≤ -Real.log (500000000000 / 9227058731981) ∧
    -Real.log (500000000000 / 9227058731981) ≤ (2915287517 / 1000000000) := by
  have h := checkLog_sound (w := (1227058731981 / 17227058731981)) (n := 12)
    (lo := (17837349 / 125000000)) (hi := (142698793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9227058731981 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9227058731981 / 8000000000000) = 1/(500000000000 / 9227058731981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (364410939 / 125000000) (2915287517 / 1000000000) (Real.log (9227058731981 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9227058731981 / 500000000000) = -Real.log (500000000000 / 9227058731981) := by
    rw [show ((9227058731981 / 500000000000) : ℝ) = ((500000000000 / 9227058731981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0181

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0182Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0182
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

theorem reflection_log_1_neg : (38927629 / 62500000) ≤ -Real.log (6400 / 11931) ∧
    -Real.log (6400 / 11931) ≤ (124568413 / 200000000) := by
  have h := checkLog_sound (w := (5531 / 18331)) (n := 12)
    (lo := (38927629 / 62500000)) (hi := (124568413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 6400) = 1/(6400 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38927629 / 62500000) (124568413 / 200000000) (Real.log (11931 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11931 / 6400) = -Real.log (6400 / 11931) := by
    rw [show ((11931 / 6400) : ℝ) = ((6400 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (998355071 / 500000000) ≤ -Real.log (869 / 6400) ∧
    -Real.log (869 / 6400) ≤ (399342029 / 200000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 869) = 1/(869 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-399342029 / 200000000) (-998355071 / 500000000) (Real.log (869 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (124249661 / 200000000) ≤ -Real.log (800 / 1489) ∧
    -Real.log (800 / 1489) ≤ (310624153 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2289)) (n := 12)
    (lo := (124249661 / 200000000)) (hi := (310624153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 800) = 1/(800 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (124249661 / 200000000) (310624153 / 500000000) (Real.log (1489 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1489 / 800) = -Real.log (800 / 1489) := by
    rw [show ((1489 / 800) : ℝ) = ((800 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79003261 / 40000000) ≤ -Real.log (111 / 800) ∧
    -Real.log (111 / 800) ≤ (246885191 / 125000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 111) = 1/(111 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-246885191 / 125000000) (-79003261 / 40000000) (Real.log (111 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (547217821 / 1000000000) ≤ -Real.log (3200 / 5531) ∧
    -Real.log (3200 / 5531) ≤ (273608911 / 500000000) := by
  have h := checkLog_sound (w := (2331 / 8731)) (n := 12)
    (lo := (547217821 / 1000000000)) (hi := (273608911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5531 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5531 / 3200) = 1/(3200 / 5531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (547217821 / 1000000000) (273608911 / 500000000) (Real.log (5531 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5531 / 3200) = -Real.log (3200 / 5531) := by
    rw [show ((5531 / 3200) : ℝ) = ((3200 / 5531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (651781481 / 500000000) ≤ -Real.log (869 / 3200) ∧
    -Real.log (869 / 3200) ≤ (325890741 / 250000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 869) = 1/(869 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-325890741 / 250000000) (-651781481 / 500000000) (Real.log (869 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (543776723 / 1000000000) ≤ -Real.log (400 / 689) ∧
    -Real.log (400 / 689) ≤ (135944181 / 250000000) := by
  have h := checkLog_sound (w := (289 / 1089)) (n := 12)
    (lo := (543776723 / 1000000000)) (hi := (135944181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 400) = 1/(400 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (543776723 / 1000000000) (135944181 / 250000000) (Real.log (689 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (689 / 400) = -Real.log (400 / 689) := by
    rw [show ((689 / 400) : ℝ) = ((400 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256386869 / 200000000) ≤ -Real.log (111 / 400) ∧
    -Real.log (111 / 400) ≤ (1281934347 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 111) = 1/(111 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1281934347 / 1000000000) (-256386869 / 200000000) (Real.log (111 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (320419317 / 500000000) ≤ -Real.log (125000 / 237259) ∧
    -Real.log (125000 / 237259) ≤ (128167727 / 200000000) := by
  have h := checkLog_sound (w := (112259 / 362259)) (n := 12)
    (lo := (320419317 / 500000000)) (hi := (128167727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237259 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237259 / 125000) = 1/(125000 / 237259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (320419317 / 500000000) (128167727 / 200000000) (Real.log (237259 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (237259 / 125000) = -Real.log (125000 / 237259) := by
    rw [show ((237259 / 125000) : ℝ) = ((125000 / 237259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (456697719 / 200000000) ≤ -Real.log (12741 / 125000) ∧
    -Real.log (12741 / 125000) ≤ (2283488599 / 1000000000) := by
  have h := checkLog_sound (w := (1442 / 14183)) (n := 12)
    (lo := (40809411 / 200000000)) (hi := (12752941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 12741) = 1/(12741 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2283488599 / 1000000000) (-456697719 / 200000000) (Real.log (12741 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (320909311 / 500000000) ≤ -Real.log (1000000 / 1899933) ∧
    -Real.log (1000000 / 1899933) ≤ (641818623 / 1000000000) := by
  have h := checkLog_sound (w := (899933 / 2899933)) (n := 12)
    (lo := (320909311 / 500000000)) (hi := (641818623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899933 / 1000000) = 1/(1000000 / 1899933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (320909311 / 500000000) (641818623 / 1000000000) (Real.log (1899933 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1899933 / 1000000) = -Real.log (1000000 / 1899933) := by
    rw [show ((1899933 / 1000000) : ℝ) = ((1000000 / 1899933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (460383063 / 200000000) ≤ -Real.log (100067 / 1000000) ∧
    -Real.log (100067 / 1000000) ≤ (2301915319 / 1000000000) := by
  have h := checkLog_sound (w := (24933 / 225067)) (n := 12)
    (lo := (8898951 / 40000000)) (hi := (13904611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100067) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100067) = 1/(100067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2301915319 / 1000000000) (-460383063 / 200000000) (Real.log (100067 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (159534907 / 250000000) ≤ -Real.log (250000 / 473239) ∧
    -Real.log (250000 / 473239) ≤ (638139629 / 1000000000) := by
  have h := checkLog_sound (w := (223239 / 723239)) (n := 12)
    (lo := (159534907 / 250000000)) (hi := (638139629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473239 / 250000) = 1/(250000 / 473239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (159534907 / 250000000) (638139629 / 1000000000) (Real.log (473239 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (473239 / 250000) = -Real.log (250000 / 473239) := by
    rw [show ((473239 / 250000) : ℝ) = ((250000 / 473239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139657207 / 62500000) ≤ -Real.log (26761 / 250000) ∧
    -Real.log (26761 / 250000) ≤ (558628829 / 250000000) := by
  have h := checkLog_sound (w := (4489 / 58011)) (n := 12)
    (lo := (38768443 / 250000000)) (hi := (155073773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26761) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 26761) = 1/(26761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-558628829 / 250000000) (-139657207 / 62500000) (Real.log (26761 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7990717 / 12500000) ≤ -Real.log (1000000 / 1895073) ∧
    -Real.log (1000000 / 1895073) ≤ (639257361 / 1000000000) := by
  have h := checkLog_sound (w := (895073 / 2895073)) (n := 12)
    (lo := (7990717 / 12500000)) (hi := (639257361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1895073 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1895073 / 1000000) = 1/(1000000 / 1895073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7990717 / 12500000) (639257361 / 1000000000) (Real.log (1895073 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1895073 / 1000000) = -Real.log (1000000 / 1895073) := by
    rw [show ((1895073 / 1000000) : ℝ) = ((1000000 / 1895073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2254490407 / 1000000000) ≤ -Real.log (104927 / 1000000) ∧
    -Real.log (104927 / 1000000) ≤ (2254490411 / 1000000000) := by
  have h := checkLog_sound (w := (20073 / 229927)) (n := 12)
    (lo := (175048867 / 1000000000)) (hi := (43762217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104927) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 104927) = 1/(104927 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2254490411 / 1000000000) (-2254490407 / 1000000000) (Real.log (104927 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2924327229 / 1000000000) ≤ -Real.log (250000000000 / 4655423436151) ∧
    -Real.log (250000000000 / 4655423436151) ≤ (1462163617 / 500000000) := by
  have h := checkLog_sound (w := (655423436151 / 8655423436151)) (n := 12)
    (lo := (151738509 / 1000000000)) (hi := (15173851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4655423436151 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4655423436151 / 4000000000000) = 1/(250000000000 / 4655423436151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2924327229 / 1000000000) (1462163617 / 500000000) (Real.log (4655423436151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4655423436151 / 250000000000) = -Real.log (250000000000 / 4655423436151) := by
    rw [show ((4655423436151 / 250000000000) : ℝ) = ((250000000000 / 4655423436151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2943733937 / 1000000000) ≤ -Real.log (100000000000 / 1898660897199) ∧
    -Real.log (100000000000 / 1898660897199) ≤ (1471866971 / 500000000) := by
  have h := checkLog_sound (w := (298660897199 / 3498660897199)) (n := 12)
    (lo := (171145217 / 1000000000)) (hi := (85572609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1898660897199 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1898660897199 / 1600000000000) = 1/(100000000000 / 1898660897199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2943733937 / 1000000000) (1471866971 / 500000000) (Real.log (1898660897199 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1898660897199 / 100000000000) = -Real.log (100000000000 / 1898660897199) := by
    rw [show ((1898660897199 / 100000000000) : ℝ) = ((100000000000 / 1898660897199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (143632747 / 50000000) ≤ -Real.log (250000000000 / 4420976420911) ∧
    -Real.log (250000000000 / 4420976420911) ≤ (574530989 / 200000000) := by
  have h := checkLog_sound (w := (420976420911 / 8420976420911)) (n := 12)
    (lo := (5003311 / 50000000)) (hi := (100066221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4420976420911 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4420976420911 / 4000000000000) = 1/(250000000000 / 4420976420911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (143632747 / 50000000) (574530989 / 200000000) (Real.log (4420976420911 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4420976420911 / 250000000000) = -Real.log (250000000000 / 4420976420911) := by
    rw [show ((4420976420911 / 250000000000) : ℝ) = ((250000000000 / 4420976420911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1446873883 / 500000000) ≤ -Real.log (125000000000 / 2257608861399) ∧
    -Real.log (125000000000 / 2257608861399) ≤ (2893747771 / 1000000000) := by
  have h := checkLog_sound (w := (257608861399 / 4257608861399)) (n := 12)
    (lo := (60579523 / 500000000)) (hi := (121159047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257608861399 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2257608861399 / 2000000000000) = 1/(125000000000 / 2257608861399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1446873883 / 500000000) (2893747771 / 1000000000) (Real.log (2257608861399 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2257608861399 / 125000000000) = -Real.log (125000000000 / 2257608861399) := by
    rw [show ((2257608861399 / 125000000000) : ℝ) = ((125000000000 / 2257608861399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0182

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0183Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0183
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

theorem reflection_log_1_neg : (124249661 / 200000000) ≤ -Real.log (800 / 1489) ∧
    -Real.log (800 / 1489) ≤ (310624153 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2289)) (n := 12)
    (lo := (124249661 / 200000000)) (hi := (310624153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 800) = 1/(800 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (124249661 / 200000000) (310624153 / 500000000) (Real.log (1489 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1489 / 800) = -Real.log (800 / 1489) := by
    rw [show ((1489 / 800) : ℝ) = ((800 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79003261 / 40000000) ≤ -Real.log (111 / 800) ∧
    -Real.log (111 / 800) ≤ (246885191 / 125000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 111) = 1/(111 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-246885191 / 125000000) (-79003261 / 40000000) (Real.log (111 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (619652001 / 1000000000) ≤ -Real.log (6400 / 11893) ∧
    -Real.log (6400 / 11893) ≤ (309826001 / 500000000) := by
  have h := checkLog_sound (w := (5493 / 18293)) (n := 12)
    (lo := (619652001 / 1000000000)) (hi := (309826001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11893 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11893 / 6400) = 1/(6400 / 11893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (619652001 / 1000000000) (309826001 / 500000000) (Real.log (11893 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11893 / 6400) = -Real.log (6400 / 11893) := by
    rw [show ((11893 / 6400) : ℝ) = ((6400 / 11893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (976955409 / 500000000) ≤ -Real.log (907 / 6400) ∧
    -Real.log (907 / 6400) ≤ (1953910821 / 1000000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 907) = 1/(907 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1953910821 / 1000000000) (-976955409 / 500000000) (Real.log (907 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (543776723 / 1000000000) ≤ -Real.log (400 / 689) ∧
    -Real.log (400 / 689) ≤ (135944181 / 250000000) := by
  have h := checkLog_sound (w := (289 / 1089)) (n := 12)
    (lo := (543776723 / 1000000000)) (hi := (135944181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 400) = 1/(400 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (543776723 / 1000000000) (135944181 / 250000000) (Real.log (689 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (689 / 400) = -Real.log (400 / 689) := by
    rw [show ((689 / 400) : ℝ) = ((400 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (256386869 / 200000000) ≤ -Real.log (111 / 400) ∧
    -Real.log (111 / 400) ≤ (1281934347 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 111) = 1/(111 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1281934347 / 1000000000) (-256386869 / 200000000) (Real.log (111 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16885117 / 31250000) ≤ -Real.log (3200 / 5493) ∧
    -Real.log (3200 / 5493) ≤ (108064749 / 200000000) := by
  have h := checkLog_sound (w := (2293 / 8693)) (n := 12)
    (lo := (16885117 / 31250000)) (hi := (108064749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5493 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5493 / 3200) = 1/(3200 / 5493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16885117 / 31250000) (108064749 / 200000000) (Real.log (5493 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5493 / 3200) = -Real.log (3200 / 5493) := by
    rw [show ((5493 / 3200) : ℝ) = ((3200 / 5493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (630381819 / 500000000) ≤ -Real.log (907 / 3200) ∧
    -Real.log (907 / 3200) ≤ (31519091 / 25000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 907) = 1/(907 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31519091 / 25000000) (-630381819 / 500000000) (Real.log (907 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (639865067 / 1000000000) ≤ -Real.log (40000 / 75849) ∧
    -Real.log (40000 / 75849) ≤ (159966267 / 250000000) := by
  have h := checkLog_sound (w := (35849 / 115849)) (n := 12)
    (lo := (639865067 / 1000000000)) (hi := (159966267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75849 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75849 / 40000) = 1/(40000 / 75849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (639865067 / 1000000000) (159966267 / 250000000) (Real.log (75849 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75849 / 40000) = -Real.log (40000 / 75849) := by
    rw [show ((75849 / 40000) : ℝ) = ((40000 / 75849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2265530183 / 1000000000) ≤ -Real.log (4151 / 40000) ∧
    -Real.log (4151 / 40000) ≤ (2265530187 / 1000000000) := by
  have h := checkLog_sound (w := (849 / 9151)) (n := 12)
    (lo := (186088643 / 1000000000)) (hi := (46522161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5000 / 4151) = 1/(4151 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2265530187 / 1000000000) (-2265530183 / 1000000000) (Real.log (4151 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16020979 / 25000000) ≤ -Real.log (1000000 / 1898073) ∧
    -Real.log (1000000 / 1898073) ≤ (640839161 / 1000000000) := by
  have h := checkLog_sound (w := (898073 / 2898073)) (n := 12)
    (lo := (16020979 / 25000000)) (hi := (640839161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1898073 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1898073 / 1000000) = 1/(1000000 / 1898073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16020979 / 25000000) (640839161 / 1000000000) (Real.log (1898073 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1898073 / 1000000) = -Real.log (1000000 / 1898073) := by
    rw [show ((1898073 / 1000000) : ℝ) = ((1000000 / 1898073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1141749203 / 500000000) ≤ -Real.log (101927 / 1000000) ∧
    -Real.log (101927 / 1000000) ≤ (228349841 / 100000000) := by
  have h := checkLog_sound (w := (23073 / 226927)) (n := 12)
    (lo := (102028433 / 500000000)) (hi := (204056867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101927) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 101927) = 1/(101927 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-228349841 / 100000000) (-1141749203 / 500000000) (Real.log (101927 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (637024347 / 1000000000) ≤ -Real.log (500000 / 945423) ∧
    -Real.log (500000 / 945423) ≤ (159256087 / 250000000) := by
  have h := checkLog_sound (w := (445423 / 1445423)) (n := 12)
    (lo := (637024347 / 1000000000)) (hi := (159256087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945423 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945423 / 500000) = 1/(500000 / 945423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (637024347 / 1000000000) (159256087 / 250000000) (Real.log (945423 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (945423 / 500000) = -Real.log (500000 / 945423) := by
    rw [show ((945423 / 500000) : ℝ) = ((500000 / 945423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (553748887 / 250000000) ≤ -Real.log (54577 / 500000) ∧
    -Real.log (54577 / 500000) ≤ (69218611 / 31250000) := by
  have h := checkLog_sound (w := (7923 / 117077)) (n := 12)
    (lo := (16944251 / 125000000)) (hi := (135554009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54577) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 54577) = 1/(54577 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-69218611 / 31250000) (-553748887 / 250000000) (Real.log (54577 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (159535039 / 250000000) ≤ -Real.log (1000000 / 1892957) ∧
    -Real.log (1000000 / 1892957) ≤ (638140157 / 1000000000) := by
  have h := checkLog_sound (w := (892957 / 2892957)) (n := 12)
    (lo := (159535039 / 250000000)) (hi := (638140157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1892957 / 1000000) = 1/(1000000 / 1892957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (159535039 / 250000000) (638140157 / 1000000000) (Real.log (1892957 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1892957 / 1000000) = -Real.log (1000000 / 1892957) := by
    rw [show ((1892957 / 1000000) : ℝ) = ((1000000 / 1892957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1117262327 / 500000000) ≤ -Real.log (107043 / 1000000) ∧
    -Real.log (107043 / 1000000) ≤ (1117262329 / 500000000) := by
  have h := checkLog_sound (w := (17957 / 232043)) (n := 12)
    (lo := (77541557 / 500000000)) (hi := (31016623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107043) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 107043) = 1/(107043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1117262329 / 500000000) (-1117262327 / 500000000) (Real.log (107043 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (11621581 / 4000000) ≤ -Real.log (125000000000 / 2284058058299) ∧
    -Real.log (125000000000 / 2284058058299) ≤ (581079051 / 200000000) := by
  have h := checkLog_sound (w := (284058058299 / 4284058058299)) (n := 12)
    (lo := (13280653 / 100000000)) (hi := (132806531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2284058058299 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2284058058299 / 2000000000000) = 1/(125000000000 / 2284058058299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (11621581 / 4000000) (581079051 / 200000000) (Real.log (2284058058299 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2284058058299 / 125000000000) = -Real.log (125000000000 / 2284058058299) := by
    rw [show ((2284058058299 / 125000000000) : ℝ) = ((125000000000 / 2284058058299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1462168783 / 500000000) ≤ -Real.log (500000000000 / 9310943125963) ∧
    -Real.log (500000000000 / 9310943125963) ≤ (2924337571 / 1000000000) := by
  have h := checkLog_sound (w := (1310943125963 / 17310943125963)) (n := 12)
    (lo := (75874423 / 500000000)) (hi := (151748847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9310943125963 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9310943125963 / 8000000000000) = 1/(500000000000 / 9310943125963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1462168783 / 500000000) (2924337571 / 1000000000) (Real.log (9310943125963 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9310943125963 / 500000000000) = -Real.log (500000000000 / 9310943125963) := by
    rw [show ((9310943125963 / 500000000000) : ℝ) = ((500000000000 / 9310943125963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (570403979 / 200000000) ≤ -Real.log (20000000000 / 346454733679) ∧
    -Real.log (20000000000 / 346454733679) ≤ (28520199 / 10000000) := by
  have h := checkLog_sound (w := (26454733679 / 666454733679)) (n := 12)
    (lo := (3177247 / 40000000)) (hi := (9928897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346454733679 / 320000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(346454733679 / 320000000000) = 1/(20000000000 / 346454733679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (570403979 / 200000000) (28520199 / 10000000) (Real.log (346454733679 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (346454733679 / 20000000000) = -Real.log (20000000000 / 346454733679) := by
    rw [show ((346454733679 / 20000000000) : ℝ) = ((20000000000 / 346454733679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (287266481 / 100000000) ≤ -Real.log (500000000000 / 8842040114721) ∧
    -Real.log (500000000000 / 8842040114721) ≤ (574532963 / 200000000) := by
  have h := checkLog_sound (w := (842040114721 / 16842040114721)) (n := 12)
    (lo := (10007609 / 100000000)) (hi := (100076091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8842040114721 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8842040114721 / 8000000000000) = 1/(500000000000 / 8842040114721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (287266481 / 100000000) (574532963 / 200000000) (Real.log (8842040114721 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8842040114721 / 500000000000) = -Real.log (500000000000 / 8842040114721) := by
    rw [show ((8842040114721 / 500000000000) : ℝ) = ((500000000000 / 8842040114721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0183

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0184Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0184
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

theorem reflection_log_1_neg : (619652001 / 1000000000) ≤ -Real.log (6400 / 11893) ∧
    -Real.log (6400 / 11893) ≤ (309826001 / 500000000) := by
  have h := checkLog_sound (w := (5493 / 18293)) (n := 12)
    (lo := (619652001 / 1000000000)) (hi := (309826001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11893 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11893 / 6400) = 1/(6400 / 11893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (619652001 / 1000000000) (309826001 / 500000000) (Real.log (11893 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11893 / 6400) = -Real.log (6400 / 11893) := by
    rw [show ((11893 / 6400) : ℝ) = ((6400 / 11893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (976955409 / 500000000) ≤ -Real.log (907 / 6400) ∧
    -Real.log (907 / 6400) ≤ (1953910821 / 1000000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 907) = 1/(907 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1953910821 / 1000000000) (-976955409 / 500000000) (Real.log (907 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (123610629 / 200000000) ≤ -Real.log (3200 / 5937) ∧
    -Real.log (3200 / 5937) ≤ (309026573 / 500000000) := by
  have h := checkLog_sound (w := (2737 / 9137)) (n := 12)
    (lo := (123610629 / 200000000)) (hi := (309026573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 3200) = 1/(3200 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (123610629 / 200000000) (309026573 / 500000000) (Real.log (5937 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5937 / 3200) = -Real.log (3200 / 5937) := by
    rw [show ((5937 / 3200) : ℝ) = ((3200 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1933179033 / 1000000000) ≤ -Real.log (463 / 3200) ∧
    -Real.log (463 / 3200) ≤ (483294759 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 463) = 1/(463 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-483294759 / 250000000) (-1933179033 / 1000000000) (Real.log (463 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16885117 / 31250000) ≤ -Real.log (3200 / 5493) ∧
    -Real.log (3200 / 5493) ≤ (108064749 / 200000000) := by
  have h := checkLog_sound (w := (2293 / 8693)) (n := 12)
    (lo := (16885117 / 31250000)) (hi := (108064749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5493 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5493 / 3200) = 1/(3200 / 5493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16885117 / 31250000) (108064749 / 200000000) (Real.log (5493 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5493 / 3200) = -Real.log (3200 / 5493) := by
    rw [show ((5493 / 3200) : ℝ) = ((3200 / 5493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (630381819 / 500000000) ≤ -Real.log (907 / 3200) ∧
    -Real.log (907 / 3200) ≤ (31519091 / 25000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 907) = 1/(907 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31519091 / 25000000) (-630381819 / 500000000) (Real.log (907 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1342147 / 2500000) ≤ -Real.log (1600 / 2737) ∧
    -Real.log (1600 / 2737) ≤ (536858801 / 1000000000) := by
  have h := checkLog_sound (w := (1137 / 4337)) (n := 12)
    (lo := (1342147 / 2500000)) (hi := (536858801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2737 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2737 / 1600) = 1/(1600 / 2737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1342147 / 2500000) (536858801 / 1000000000) (Real.log (2737 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2737 / 1600) = -Real.log (1600 / 2737) := by
    rw [show ((2737 / 1600) : ℝ) = ((1600 / 2737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1240031853 / 1000000000) ≤ -Real.log (463 / 1600) ∧
    -Real.log (463 / 1600) ≤ (248006371 / 200000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 463) = 1/(463 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248006371 / 200000000) (-1240031853 / 1000000000) (Real.log (463 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (319448707 / 500000000) ≤ -Real.log (1000000 / 1894391) ∧
    -Real.log (1000000 / 1894391) ≤ (127779483 / 200000000) := by
  have h := checkLog_sound (w := (894391 / 2894391)) (n := 12)
    (lo := (319448707 / 500000000)) (hi := (127779483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1894391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1894391 / 1000000) = 1/(1000000 / 1894391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (319448707 / 500000000) (127779483 / 200000000) (Real.log (1894391 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1894391 / 1000000) = -Real.log (1000000 / 1894391) := by
    rw [show ((1894391 / 1000000) : ℝ) = ((1000000 / 1894391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1124005841 / 500000000) ≤ -Real.log (105609 / 1000000) ∧
    -Real.log (105609 / 1000000) ≤ (1124005843 / 500000000) := by
  have h := checkLog_sound (w := (19391 / 230609)) (n := 12)
    (lo := (84285071 / 500000000)) (hi := (168570143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105609) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 105609) = 1/(105609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1124005843 / 500000000) (-1124005841 / 500000000) (Real.log (105609 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127973119 / 200000000) ≤ -Real.log (500000 / 948113) ∧
    -Real.log (500000 / 948113) ≤ (159966399 / 250000000) := by
  have h := checkLog_sound (w := (448113 / 1448113)) (n := 12)
    (lo := (127973119 / 200000000)) (hi := (159966399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948113 / 500000) = 1/(500000 / 948113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127973119 / 200000000) (159966399 / 250000000) (Real.log (948113 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (948113 / 500000) = -Real.log (500000 / 948113) := by
    rw [show ((948113 / 500000) : ℝ) = ((500000 / 948113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2265539819 / 1000000000) ≤ -Real.log (51887 / 500000) ∧
    -Real.log (51887 / 500000) ≤ (2265539823 / 1000000000) := by
  have h := checkLog_sound (w := (10613 / 114387)) (n := 12)
    (lo := (186098279 / 1000000000)) (hi := (4652457 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 51887) = 1/(51887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2265539823 / 1000000000) (-2265539819 / 1000000000) (Real.log (51887 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (31795497 / 50000000) ≤ -Real.log (50000 / 94437) ∧
    -Real.log (50000 / 94437) ≤ (635909941 / 1000000000) := by
  have h := checkLog_sound (w := (44437 / 144437)) (n := 12)
    (lo := (31795497 / 50000000)) (hi := (635909941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94437 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94437 / 50000) = 1/(50000 / 94437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (31795497 / 50000000) (635909941 / 1000000000) (Real.log (94437 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (94437 / 50000) = -Real.log (50000 / 94437) := by
    rw [show ((94437 / 50000) : ℝ) = ((50000 / 94437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (68621421 / 31250000) ≤ -Real.log (5563 / 50000) ∧
    -Real.log (5563 / 50000) ≤ (548971369 / 250000000) := by
  have h := checkLog_sound (w := (687 / 11813)) (n := 12)
    (lo := (29110983 / 250000000)) (hi := (116443933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5563) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 5563) = 1/(5563 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-548971369 / 250000000) (-68621421 / 31250000) (Real.log (5563 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (159256219 / 250000000) ≤ -Real.log (1000000 / 1890847) ∧
    -Real.log (1000000 / 1890847) ≤ (637024877 / 1000000000) := by
  have h := checkLog_sound (w := (890847 / 2890847)) (n := 12)
    (lo := (159256219 / 250000000)) (hi := (637024877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1890847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1890847 / 1000000) = 1/(1000000 / 1890847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (159256219 / 250000000) (637024877 / 1000000000) (Real.log (1890847 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1890847 / 1000000) = -Real.log (1000000 / 1890847) := by
    rw [show ((1890847 / 1000000) : ℝ) = ((1000000 / 1890847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2215004709 / 1000000000) ≤ -Real.log (109153 / 1000000) ∧
    -Real.log (109153 / 1000000) ≤ (2215004713 / 1000000000) := by
  have h := checkLog_sound (w := (15847 / 234153)) (n := 12)
    (lo := (135563169 / 1000000000)) (hi := (13556317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 109153) = 1/(109153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2215004713 / 1000000000) (-2215004709 / 1000000000) (Real.log (109153 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (360863637 / 125000000) ≤ -Real.log (500000000000 / 8968889962029) ∧
    -Real.log (500000000000 / 8968889962029) ≤ (2886909101 / 1000000000) := by
  have h := checkLog_sound (w := (968889962029 / 16968889962029)) (n := 12)
    (lo := (14290047 / 125000000)) (hi := (114320377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8968889962029 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8968889962029 / 8000000000000) = 1/(500000000000 / 8968889962029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (360863637 / 125000000) (2886909101 / 1000000000) (Real.log (8968889962029 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8968889962029 / 500000000000) = -Real.log (500000000000 / 8968889962029) := by
    rw [show ((8968889962029 / 500000000000) : ℝ) = ((500000000000 / 8968889962029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1452702707 / 500000000) ≤ -Real.log (62500000000 / 1142040636383) ∧
    -Real.log (62500000000 / 1142040636383) ≤ (2905405419 / 1000000000) := by
  have h := checkLog_sound (w := (142040636383 / 2142040636383)) (n := 12)
    (lo := (66408347 / 500000000)) (hi := (26563339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142040636383 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1142040636383 / 1000000000000) = 1/(62500000000 / 1142040636383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1452702707 / 500000000) (2905405419 / 1000000000) (Real.log (1142040636383 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1142040636383 / 62500000000) = -Real.log (62500000000 / 1142040636383) := by
    rw [show ((1142040636383 / 62500000000) : ℝ) = ((62500000000 / 1142040636383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (707948853 / 250000000) ≤ -Real.log (250000000000 / 4243978069387) ∧
    -Real.log (250000000000 / 4243978069387) ≤ (2831795417 / 1000000000) := by
  have h := checkLog_sound (w := (243978069387 / 8243978069387)) (n := 12)
    (lo := (14801673 / 250000000)) (hi := (59206693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4243978069387 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4243978069387 / 4000000000000) = 1/(250000000000 / 4243978069387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (707948853 / 250000000) (2831795417 / 1000000000) (Real.log (4243978069387 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4243978069387 / 250000000000) = -Real.log (250000000000 / 4243978069387) := by
    rw [show ((4243978069387 / 250000000000) : ℝ) = ((250000000000 / 4243978069387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (570405917 / 200000000) ≤ -Real.log (100000000000 / 1732290454683) ∧
    -Real.log (100000000000 / 1732290454683) ≤ (285202959 / 100000000) := by
  have h := checkLog_sound (w := (132290454683 / 3332290454683)) (n := 12)
    (lo := (15888173 / 200000000)) (hi := (39720433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1732290454683 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1732290454683 / 1600000000000) = 1/(100000000000 / 1732290454683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (570405917 / 200000000) (285202959 / 100000000) (Real.log (1732290454683 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1732290454683 / 100000000000) = -Real.log (100000000000 / 1732290454683) := by
    rw [show ((1732290454683 / 100000000000) : ℝ) = ((100000000000 / 1732290454683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0184

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0185Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0185
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

theorem reflection_log_1_neg : (123610629 / 200000000) ≤ -Real.log (3200 / 5937) ∧
    -Real.log (3200 / 5937) ≤ (309026573 / 500000000) := by
  have h := checkLog_sound (w := (2737 / 9137)) (n := 12)
    (lo := (123610629 / 200000000)) (hi := (309026573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 3200) = 1/(3200 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (123610629 / 200000000) (309026573 / 500000000) (Real.log (5937 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5937 / 3200) = -Real.log (3200 / 5937) := by
    rw [show ((5937 / 3200) : ℝ) = ((3200 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1933179033 / 1000000000) ≤ -Real.log (463 / 3200) ∧
    -Real.log (463 / 3200) ≤ (483294759 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 463) = 1/(463 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-483294759 / 250000000) (-1933179033 / 1000000000) (Real.log (463 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1342147 / 2500000) ≤ -Real.log (1600 / 2737) ∧
    -Real.log (1600 / 2737) ≤ (536858801 / 1000000000) := by
  have h := checkLog_sound (w := (1137 / 4337)) (n := 12)
    (lo := (1342147 / 2500000)) (hi := (536858801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2737 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2737 / 1600) = 1/(1600 / 2737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1342147 / 2500000) (536858801 / 1000000000) (Real.log (2737 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2737 / 1600) = -Real.log (1600 / 2737) := by
    rw [show ((2737 / 1600) : ℝ) = ((1600 / 2737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1240031853 / 1000000000) ≤ -Real.log (463 / 1600) ∧
    -Real.log (463 / 1600) ≤ (248006371 / 200000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 463) = 1/(463 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248006371 / 200000000) (-1240031853 / 1000000000) (Real.log (463 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (637935693 / 1000000000) ≤ -Real.log (100000 / 189257) ∧
    -Real.log (100000 / 189257) ≤ (318967847 / 500000000) := by
  have h := checkLog_sound (w := (89257 / 289257)) (n := 12)
    (lo := (637935693 / 1000000000)) (hi := (318967847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189257 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189257 / 100000) = 1/(100000 / 189257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (637935693 / 1000000000) (318967847 / 500000000) (Real.log (189257 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (189257 / 100000) = -Real.log (100000 / 189257) := by
    rw [show ((189257 / 100000) : ℝ) = ((100000 / 189257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (557728951 / 250000000) ≤ -Real.log (10743 / 100000) ∧
    -Real.log (10743 / 100000) ≤ (69716119 / 31250000) := by
  have h := checkLog_sound (w := (1757 / 23243)) (n := 12)
    (lo := (18934283 / 125000000)) (hi := (30294853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10743) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 10743) = 1/(10743 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69716119 / 31250000) (-557728951 / 250000000) (Real.log (10743 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (319448971 / 500000000) ≤ -Real.log (125000 / 236799) ∧
    -Real.log (125000 / 236799) ≤ (638897943 / 1000000000) := by
  have h := checkLog_sound (w := (111799 / 361799)) (n := 12)
    (lo := (319448971 / 500000000)) (hi := (638897943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236799 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236799 / 125000) = 1/(125000 / 236799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (319448971 / 500000000) (638897943 / 1000000000) (Real.log (236799 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (236799 / 125000) = -Real.log (125000 / 236799) := by
    rw [show ((236799 / 125000) : ℝ) = ((125000 / 236799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2248021151 / 1000000000) ≤ -Real.log (13201 / 125000) ∧
    -Real.log (13201 / 125000) ≤ (449604231 / 200000000) := by
  have h := checkLog_sound (w := (1212 / 14413)) (n := 12)
    (lo := (168579611 / 1000000000)) (hi := (42144903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13201) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13201) = 1/(13201 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-449604231 / 200000000) (-2248021151 / 1000000000) (Real.log (13201 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (634796939 / 1000000000) ≤ -Real.log (1000000 / 1886639) ∧
    -Real.log (1000000 / 1886639) ≤ (31739847 / 50000000) := by
  have h := checkLog_sound (w := (886639 / 2886639)) (n := 12)
    (lo := (634796939 / 1000000000)) (hi := (31739847 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1886639 / 1000000) = 1/(1000000 / 1886639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (634796939 / 1000000000) (31739847 / 50000000) (Real.log (1886639 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1886639 / 1000000) = -Real.log (1000000 / 1886639) := by
    rw [show ((1886639 / 1000000) : ℝ) = ((1000000 / 1886639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (108858893 / 50000000) ≤ -Real.log (113361 / 1000000) ∧
    -Real.log (113361 / 1000000) ≤ (272147233 / 125000000) := by
  have h := checkLog_sound (w := (11639 / 238361)) (n := 12)
    (lo := (152713 / 1562500)) (hi := (97736321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113361) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 113361) = 1/(113361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-272147233 / 125000000) (-108858893 / 50000000) (Real.log (113361 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (635910469 / 1000000000) ≤ -Real.log (1000000 / 1888741) ∧
    -Real.log (1000000 / 1888741) ≤ (63591047 / 100000000) := by
  have h := checkLog_sound (w := (888741 / 2888741)) (n := 12)
    (lo := (635910469 / 1000000000)) (hi := (63591047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1888741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1888741 / 1000000) = 1/(1000000 / 1888741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (635910469 / 1000000000) (63591047 / 100000000) (Real.log (1888741 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1888741 / 1000000) = -Real.log (1000000 / 1888741) := by
    rw [show ((1888741 / 1000000) : ℝ) = ((1000000 / 1888741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (109794723 / 50000000) ≤ -Real.log (111259 / 1000000) ∧
    -Real.log (111259 / 1000000) ≤ (34310851 / 15625000) := by
  have h := checkLog_sound (w := (13741 / 236259)) (n := 12)
    (lo := (2911323 / 25000000)) (hi := (116452921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 111259) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 111259) = 1/(111259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-34310851 / 15625000) (-109794723 / 50000000) (Real.log (111259 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2868851497 / 1000000000) ≤ -Real.log (500000000000 / 8808386856557) ∧
    -Real.log (500000000000 / 8808386856557) ≤ (1434425751 / 500000000) := by
  have h := checkLog_sound (w := (808386856557 / 16808386856557)) (n := 12)
    (lo := (96262777 / 1000000000)) (hi := (48131389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8808386856557 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8808386856557 / 8000000000000) = 1/(500000000000 / 8808386856557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2868851497 / 1000000000) (1434425751 / 500000000) (Real.log (8808386856557 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8808386856557 / 500000000000) = -Real.log (500000000000 / 8808386856557) := by
    rw [show ((8808386856557 / 500000000000) : ℝ) = ((500000000000 / 8808386856557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2886919093 / 1000000000) ≤ -Real.log (125000000000 / 2242244905689) ∧
    -Real.log (125000000000 / 2242244905689) ≤ (1443459549 / 500000000) := by
  have h := checkLog_sound (w := (242244905689 / 4242244905689)) (n := 12)
    (lo := (114330373 / 1000000000)) (hi := (57165187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2242244905689 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2242244905689 / 2000000000000) = 1/(125000000000 / 2242244905689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2886919093 / 1000000000) (1443459549 / 500000000) (Real.log (2242244905689 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2242244905689 / 125000000000) = -Real.log (125000000000 / 2242244905689) := by
    rw [show ((2242244905689 / 125000000000) : ℝ) = ((125000000000 / 2242244905689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2811974799 / 1000000000) ≤ -Real.log (500000000000 / 8321375958221) ∧
    -Real.log (500000000000 / 8321375958221) ≤ (702993701 / 250000000) := by
  have h := checkLog_sound (w := (321375958221 / 16321375958221)) (n := 12)
    (lo := (39386079 / 1000000000)) (hi := (246163 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8321375958221 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8321375958221 / 8000000000000) = 1/(500000000000 / 8321375958221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2811974799 / 1000000000) (702993701 / 250000000) (Real.log (8321375958221 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8321375958221 / 500000000000) = -Real.log (500000000000 / 8321375958221) := by
    rw [show ((8321375958221 / 500000000000) : ℝ) = ((500000000000 / 8321375958221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2831804929 / 1000000000) ≤ -Real.log (62500000000 / 1061004615357) ∧
    -Real.log (62500000000 / 1061004615357) ≤ (1415902467 / 500000000) := by
  have h := checkLog_sound (w := (61004615357 / 2061004615357)) (n := 12)
    (lo := (59216209 / 1000000000)) (hi := (5921621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061004615357 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1061004615357 / 1000000000000) = 1/(62500000000 / 1061004615357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2831804929 / 1000000000) (1415902467 / 500000000) (Real.log (1061004615357 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1061004615357 / 62500000000) = -Real.log (62500000000 / 1061004615357) := by
    rw [show ((1061004615357 / 62500000000) : ℝ) = ((62500000000 / 1061004615357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0185

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0186Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0186
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

theorem reflection_log_1_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2401749 / 3906250) ≤ -Real.log (1600 / 2959) ∧
    -Real.log (1600 / 2959) ≤ (122969549 / 200000000) := by
  have h := checkLog_sound (w := (1359 / 4559)) (n := 12)
    (lo := (2401749 / 3906250)) (hi := (122969549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2959 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2959 / 1600) = 1/(1600 / 2959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2401749 / 3906250) (122969549 / 200000000) (Real.log (2959 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2959 / 1600) = -Real.log (1600 / 2959) := by
    rw [show ((2959 / 1600) : ℝ) = ((1600 / 2959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1892961973 / 1000000000) ≤ -Real.log (241 / 1600) ∧
    -Real.log (241 / 1600) ≤ (236620247 / 125000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 241) = 1/(241 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236620247 / 125000000) (-1892961973 / 1000000000) (Real.log (241 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (264946343 / 500000000) ≤ -Real.log (800 / 1359) ∧
    -Real.log (800 / 1359) ≤ (529892687 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 2159)) (n := 12)
    (lo := (264946343 / 500000000)) (hi := (529892687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 800) = 1/(800 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (264946343 / 500000000) (529892687 / 1000000000) (Real.log (1359 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1359 / 800) = -Real.log (800 / 1359) := by
    rw [show ((1359 / 800) : ℝ) = ((800 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1199814793 / 1000000000) ≤ -Real.log (241 / 800) ∧
    -Real.log (241 / 800) ≤ (239962959 / 200000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 241) = 1/(241 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-239962959 / 200000000) (-1199814793 / 1000000000) (Real.log (241 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (636980451 / 1000000000) ≤ -Real.log (1000000 / 1890763) ∧
    -Real.log (1000000 / 1890763) ≤ (159245113 / 250000000) := by
  have h := checkLog_sound (w := (890763 / 2890763)) (n := 12)
    (lo := (636980451 / 1000000000)) (hi := (159245113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1890763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1890763 / 1000000) = 1/(1000000 / 1890763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (636980451 / 1000000000) (159245113 / 250000000) (Real.log (1890763 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1890763 / 1000000) = -Real.log (1000000 / 1890763) := by
    rw [show ((1890763 / 1000000) : ℝ) = ((1000000 / 1890763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2214235443 / 1000000000) ≤ -Real.log (109237 / 1000000) ∧
    -Real.log (109237 / 1000000) ≤ (2214235447 / 1000000000) := by
  have h := checkLog_sound (w := (15763 / 234237)) (n := 12)
    (lo := (134793903 / 1000000000)) (hi := (8424619 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109237) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 109237) = 1/(109237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2214235447 / 1000000000) (-2214235443 / 1000000000) (Real.log (109237 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318968111 / 500000000) ≤ -Real.log (1000000 / 1892571) ∧
    -Real.log (1000000 / 1892571) ≤ (637936223 / 1000000000) := by
  have h := checkLog_sound (w := (892571 / 2892571)) (n := 12)
    (lo := (318968111 / 500000000)) (hi := (637936223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1892571 / 1000000) = 1/(1000000 / 1892571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318968111 / 500000000) (637936223 / 1000000000) (Real.log (1892571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1892571 / 1000000) = -Real.log (1000000 / 1892571) := by
    rw [show ((1892571 / 1000000) : ℝ) = ((1000000 / 1892571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2230925113 / 1000000000) ≤ -Real.log (107429 / 1000000) ∧
    -Real.log (107429 / 1000000) ≤ (2230925117 / 1000000000) := by
  have h := checkLog_sound (w := (17571 / 232429)) (n := 12)
    (lo := (151483573 / 1000000000)) (hi := (75741787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 107429) = 1/(107429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2230925117 / 1000000000) (-2230925113 / 1000000000) (Real.log (107429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (633685881 / 1000000000) ≤ -Real.log (15625 / 29446) ∧
    -Real.log (15625 / 29446) ≤ (316842941 / 500000000) := by
  have h := checkLog_sound (w := (13821 / 45071)) (n := 12)
    (lo := (633685881 / 1000000000)) (hi := (316842941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29446 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29446 / 15625) = 1/(15625 / 29446) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (633685881 / 1000000000) (316842941 / 500000000) (Real.log (29446 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (29446 / 15625) = -Real.log (15625 / 29446) := by
    rw [show ((29446 / 15625) : ℝ) = ((15625 / 29446) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (539716443 / 250000000) ≤ -Real.log (1804 / 15625) ∧
    -Real.log (1804 / 15625) ≤ (134929111 / 62500000) := by
  have h := checkLog_sound (w := (1193 / 30057)) (n := 12)
    (lo := (9928029 / 125000000)) (hi := (79424233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14432) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 14432) = 1/(1804 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134929111 / 62500000) (-539716443 / 250000000) (Real.log (1804 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (634797469 / 1000000000) ≤ -Real.log (12500 / 23583) ∧
    -Real.log (12500 / 23583) ≤ (63479747 / 100000000) := by
  have h := checkLog_sound (w := (11083 / 36083)) (n := 12)
    (lo := (634797469 / 1000000000)) (hi := (63479747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23583 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23583 / 12500) = 1/(12500 / 23583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (634797469 / 1000000000) (63479747 / 100000000) (Real.log (23583 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (23583 / 12500) = -Real.log (12500 / 23583) := by
    rw [show ((23583 / 12500) : ℝ) = ((12500 / 23583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2177186681 / 1000000000) ≤ -Real.log (1417 / 12500) ∧
    -Real.log (1417 / 12500) ≤ (435437337 / 200000000) := by
  have h := checkLog_sound (w := (291 / 5959)) (n := 12)
    (lo := (97745141 / 1000000000)) (hi := (48872571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2834) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2834) = 1/(1417 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-435437337 / 200000000) (-2177186681 / 1000000000) (Real.log (1417 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1425607947 / 500000000) ≤ -Real.log (500000000000 / 8654407389437) ∧
    -Real.log (500000000000 / 8654407389437) ≤ (2851215899 / 1000000000) := by
  have h := checkLog_sound (w := (654407389437 / 16654407389437)) (n := 12)
    (lo := (39313587 / 500000000)) (hi := (3145087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8654407389437 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8654407389437 / 8000000000000) = 1/(500000000000 / 8654407389437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1425607947 / 500000000) (2851215899 / 1000000000) (Real.log (8654407389437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8654407389437 / 500000000000) = -Real.log (500000000000 / 8654407389437) := by
    rw [show ((8654407389437 / 500000000000) : ℝ) = ((500000000000 / 8654407389437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1434430667 / 500000000) ≤ -Real.log (500000000000 / 8808473503431) ∧
    -Real.log (500000000000 / 8808473503431) ≤ (2868861339 / 1000000000) := by
  have h := checkLog_sound (w := (808473503431 / 16808473503431)) (n := 12)
    (lo := (48136307 / 500000000)) (hi := (19254523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8808473503431 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8808473503431 / 8000000000000) = 1/(500000000000 / 8808473503431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1434430667 / 500000000) (2868861339 / 1000000000) (Real.log (8808473503431 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8808473503431 / 500000000000) = -Real.log (500000000000 / 8808473503431) := by
    rw [show ((8808473503431 / 500000000000) : ℝ) = ((500000000000 / 8808473503431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2792551653 / 1000000000) ≤ -Real.log (500000000000 / 8161308203991) ∧
    -Real.log (500000000000 / 8161308203991) ≤ (1396275829 / 500000000) := by
  have h := checkLog_sound (w := (161308203991 / 16161308203991)) (n := 12)
    (lo := (19962933 / 1000000000)) (hi := (9981467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8161308203991 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8161308203991 / 8000000000000) = 1/(500000000000 / 8161308203991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2792551653 / 1000000000) (1396275829 / 500000000) (Real.log (8161308203991 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8161308203991 / 500000000000) = -Real.log (500000000000 / 8161308203991) := by
    rw [show ((8161308203991 / 500000000000) : ℝ) = ((500000000000 / 8161308203991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (56239683 / 20000000) ≤ -Real.log (500000000000 / 8321453775583) ∧
    -Real.log (500000000000 / 8321453775583) ≤ (562396831 / 200000000) := by
  have h := checkLog_sound (w := (321453775583 / 16321453775583)) (n := 12)
    (lo := (3939543 / 100000000)) (hi := (39395431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8321453775583 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8321453775583 / 8000000000000) = 1/(500000000000 / 8321453775583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (56239683 / 20000000) (562396831 / 200000000) (Real.log (8321453775583 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8321453775583 / 500000000000) = -Real.log (500000000000 / 8321453775583) := by
    rw [show ((8321453775583 / 500000000000) : ℝ) = ((500000000000 / 8321453775583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0186

end


