-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0121Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0121Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:33:46.173367+00:00
-- url     : https://prove2.me/theorems/d957c9e6-35a3-4c55-b1fd-80d185a3075e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0121Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0122Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0121Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0125Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0126Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0121Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0125Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0126Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0121Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0122Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0123Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0124Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0125Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0126Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0121Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0122Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0123Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0124Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0125Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0126Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0121Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0121
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

theorem reflection_log_1_neg : (157804389 / 500000000) ≤ -Real.log (256 / 351) ∧
    -Real.log (256 / 351) ≤ (315608779 / 1000000000) := by
  have h := checkLog_sound (w := (95 / 607)) (n := 12)
    (lo := (157804389 / 500000000)) (hi := (315608779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 256) = 1/(256 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157804389 / 500000000) (315608779 / 1000000000) (Real.log (351 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (351 / 256) = -Real.log (256 / 351) := by
    rw [show ((351 / 256) : ℝ) = ((256 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (463773079 / 1000000000) ≤ -Real.log (161 / 256) ∧
    -Real.log (161 / 256) ≤ (11594327 / 25000000) := by
  have h := checkLog_sound (w := (95 / 417)) (n := 12)
    (lo := (463773079 / 1000000000)) (hi := (11594327 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 161) = 1/(161 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11594327 / 25000000) (-463773079 / 1000000000) (Real.log (161 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19672107 / 62500000) ≤ -Real.log (2560 / 3507) ∧
    -Real.log (2560 / 3507) ≤ (314753713 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 6067)) (n := 12)
    (lo := (19672107 / 62500000)) (hi := (314753713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3507 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3507 / 2560) = 1/(2560 / 3507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19672107 / 62500000) (314753713 / 1000000000) (Real.log (3507 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3507 / 2560) = -Real.log (2560 / 3507) := by
    rw [show ((3507 / 2560) : ℝ) = ((2560 / 3507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (461911459 / 1000000000) ≤ -Real.log (1613 / 2560) ∧
    -Real.log (1613 / 2560) ≤ (23095573 / 50000000) := by
  have h := checkLog_sound (w := (947 / 4173)) (n := 12)
    (lo := (461911459 / 1000000000)) (hi := (23095573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1613) = 1/(1613 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-23095573 / 50000000) (-461911459 / 1000000000) (Real.log (1613 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (555141507 / 1000000000) ≤ -Real.log (128 / 223) ∧
    -Real.log (128 / 223) ≤ (138785377 / 250000000) := by
  have h := checkLog_sound (w := (95 / 351)) (n := 12)
    (lo := (555141507 / 1000000000)) (hi := (138785377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223 / 128) = 1/(128 / 223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (555141507 / 1000000000) (138785377 / 250000000) (Real.log (223 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (223 / 128) = -Real.log (128 / 223) := by
    rw [show ((223 / 128) : ℝ) = ((128 / 223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1355522701 / 1000000000) ≤ -Real.log (33 / 128) ∧
    -Real.log (33 / 128) ≤ (1355522703 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 33) = 1/(33 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1355522703 / 1000000000) (-1355522701 / 1000000000) (Real.log (33 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (55379531 / 100000000) ≤ -Real.log (1280 / 2227) ∧
    -Real.log (1280 / 2227) ≤ (553795311 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 3507)) (n := 12)
    (lo := (55379531 / 100000000)) (hi := (553795311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2227 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2227 / 1280) = 1/(1280 / 2227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (55379531 / 100000000) (553795311 / 1000000000) (Real.log (2227 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2227 / 1280) = -Real.log (1280 / 2227) := by
    rw [show ((2227 / 1280) : ℝ) = ((1280 / 2227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (673236433 / 500000000) ≤ -Real.log (333 / 1280) ∧
    -Real.log (333 / 1280) ≤ (336618217 / 250000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 333) = 1/(333 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-336618217 / 250000000) (-673236433 / 500000000) (Real.log (333 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (431174439 / 1000000000) ≤ -Real.log (125000 / 192383) ∧
    -Real.log (125000 / 192383) ≤ (10779361 / 25000000) := by
  have h := checkLog_sound (w := (67383 / 317383)) (n := 12)
    (lo := (431174439 / 1000000000)) (hi := (10779361 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192383 / 125000) = 1/(125000 / 192383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (431174439 / 1000000000) (10779361 / 25000000) (Real.log (192383 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (192383 / 125000) = -Real.log (125000 / 192383) := by
    rw [show ((192383 / 125000) : ℝ) = ((125000 / 192383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (774496073 / 1000000000) ≤ -Real.log (57617 / 125000) ∧
    -Real.log (57617 / 125000) ≤ (30979843 / 40000000) := by
  have h := checkLog_sound (w := (4883 / 120117)) (n := 12)
    (lo := (81348893 / 1000000000)) (hi := (40674447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 57617) = 1/(57617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30979843 / 40000000) (-774496073 / 1000000000) (Real.log (57617 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (432375097 / 1000000000) ≤ -Real.log (1000000 / 1540913) ∧
    -Real.log (1000000 / 1540913) ≤ (216187549 / 500000000) := by
  have h := checkLog_sound (w := (540913 / 2540913)) (n := 12)
    (lo := (432375097 / 1000000000)) (hi := (216187549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1540913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1540913 / 1000000) = 1/(1000000 / 1540913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (432375097 / 1000000000) (216187549 / 500000000) (Real.log (1540913 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1540913 / 1000000) = -Real.log (1000000 / 1540913) := by
    rw [show ((1540913 / 1000000) : ℝ) = ((1000000 / 1540913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (778515543 / 1000000000) ≤ -Real.log (459087 / 1000000) ∧
    -Real.log (459087 / 1000000) ≤ (155703109 / 200000000) := by
  have h := checkLog_sound (w := (40913 / 959087)) (n := 12)
    (lo := (85368363 / 1000000000)) (hi := (21342091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459087) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 459087) = 1/(459087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-155703109 / 200000000) (-778515543 / 1000000000) (Real.log (459087 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69332881 / 200000000) ≤ -Real.log (500000 / 707171) ∧
    -Real.log (500000 / 707171) ≤ (173332203 / 500000000) := by
  have h := checkLog_sound (w := (207171 / 1207171)) (n := 12)
    (lo := (69332881 / 200000000)) (hi := (173332203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707171 / 500000) = 1/(500000 / 707171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69332881 / 200000000) (173332203 / 500000000) (Real.log (707171 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (707171 / 500000) = -Real.log (500000 / 707171) := by
    rw [show ((707171 / 500000) : ℝ) = ((500000 / 707171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (535019277 / 1000000000) ≤ -Real.log (292829 / 500000) ∧
    -Real.log (292829 / 500000) ≤ (267509639 / 500000000) := by
  have h := checkLog_sound (w := (207171 / 792829)) (n := 12)
    (lo := (535019277 / 1000000000)) (hi := (267509639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292829) = 1/(292829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267509639 / 500000000) (-535019277 / 1000000000) (Real.log (292829 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (347842351 / 1000000000) ≤ -Real.log (1000000 / 1416009) ∧
    -Real.log (1000000 / 1416009) ≤ (21740147 / 62500000) := by
  have h := checkLog_sound (w := (416009 / 2416009)) (n := 12)
    (lo := (347842351 / 1000000000)) (hi := (21740147 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1416009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1416009 / 1000000) = 1/(1000000 / 1416009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (347842351 / 1000000000) (21740147 / 62500000) (Real.log (1416009 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1416009 / 1000000) = -Real.log (1000000 / 1416009) := by
    rw [show ((1416009 / 1000000) : ℝ) = ((1000000 / 1416009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (537869707 / 1000000000) ≤ -Real.log (583991 / 1000000) ∧
    -Real.log (583991 / 1000000) ≤ (134467427 / 250000000) := by
  have h := checkLog_sound (w := (416009 / 1583991)) (n := 12)
    (lo := (537869707 / 1000000000)) (hi := (134467427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 583991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 583991) = 1/(583991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-134467427 / 250000000) (-537869707 / 1000000000) (Real.log (583991 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1205670513 / 1000000000) ≤ -Real.log (250000000000 / 834749292743) ∧
    -Real.log (250000000000 / 834749292743) ≤ (241134103 / 200000000) := by
  have h := checkLog_sound (w := (334749292743 / 1334749292743)) (n := 12)
    (lo := (512523333 / 1000000000)) (hi := (256261667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834749292743 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(834749292743 / 500000000000) = 1/(250000000000 / 834749292743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1205670513 / 1000000000) (241134103 / 200000000) (Real.log (834749292743 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (834749292743 / 250000000000) = -Real.log (250000000000 / 834749292743) := by
    rw [show ((834749292743 / 250000000000) : ℝ) = ((250000000000 / 834749292743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1210890641 / 1000000000) ≤ -Real.log (250000000000 / 839118184571) ∧
    -Real.log (250000000000 / 839118184571) ≤ (1210890643 / 1000000000) := by
  have h := checkLog_sound (w := (339118184571 / 1339118184571)) (n := 12)
    (lo := (517743461 / 1000000000)) (hi := (258871731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839118184571 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(839118184571 / 500000000000) = 1/(250000000000 / 839118184571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1210890641 / 1000000000) (1210890643 / 1000000000) (Real.log (839118184571 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (839118184571 / 250000000000) = -Real.log (250000000000 / 839118184571) := by
    rw [show ((839118184571 / 250000000000) : ℝ) = ((250000000000 / 839118184571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (440841841 / 500000000) ≤ -Real.log (100000000000 / 241496231589) ∧
    -Real.log (100000000000 / 241496231589) ≤ (220420921 / 250000000) := by
  have h := checkLog_sound (w := (41496231589 / 441496231589)) (n := 12)
    (lo := (94268251 / 500000000)) (hi := (188536503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241496231589 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(241496231589 / 200000000000) = 1/(100000000000 / 241496231589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (440841841 / 500000000) (220420921 / 250000000) (Real.log (241496231589 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (241496231589 / 100000000000) = -Real.log (100000000000 / 241496231589) := by
    rw [show ((241496231589 / 100000000000) : ℝ) = ((100000000000 / 241496231589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (885712057 / 1000000000) ≤ -Real.log (500000000000 / 1212355156159) ∧
    -Real.log (500000000000 / 1212355156159) ≤ (885712059 / 1000000000) := by
  have h := checkLog_sound (w := (212355156159 / 2212355156159)) (n := 12)
    (lo := (192564877 / 1000000000)) (hi := (96282439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212355156159 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212355156159 / 1000000000000) = 1/(500000000000 / 1212355156159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (885712057 / 1000000000) (885712059 / 1000000000) (Real.log (1212355156159 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1212355156159 / 500000000000) = -Real.log (500000000000 / 1212355156159) := by
    rw [show ((1212355156159 / 500000000000) : ℝ) = ((500000000000 / 1212355156159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0121

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0122Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0122
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

theorem reflection_log_1_neg : (19672107 / 62500000) ≤ -Real.log (2560 / 3507) ∧
    -Real.log (2560 / 3507) ≤ (314753713 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 6067)) (n := 12)
    (lo := (19672107 / 62500000)) (hi := (314753713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3507 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3507 / 2560) = 1/(2560 / 3507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19672107 / 62500000) (314753713 / 1000000000) (Real.log (3507 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3507 / 2560) = -Real.log (2560 / 3507) := by
    rw [show ((3507 / 2560) : ℝ) = ((2560 / 3507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (461911459 / 1000000000) ≤ -Real.log (1613 / 2560) ∧
    -Real.log (1613 / 2560) ≤ (23095573 / 50000000) := by
  have h := checkLog_sound (w := (947 / 4173)) (n := 12)
    (lo := (461911459 / 1000000000)) (hi := (23095573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1613) = 1/(1613 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-23095573 / 50000000) (-461911459 / 1000000000) (Real.log (1613 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156948957 / 500000000) ≤ -Real.log (160 / 219) ∧
    -Real.log (160 / 219) ≤ (62779583 / 200000000) := by
  have h := checkLog_sound (w := (59 / 379)) (n := 12)
    (lo := (156948957 / 500000000)) (hi := (62779583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 160) = 1/(160 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156948957 / 500000000) (62779583 / 200000000) (Real.log (219 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (219 / 160) = -Real.log (160 / 219) := by
    rw [show ((219 / 160) : ℝ) = ((160 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230026649 / 500000000) ≤ -Real.log (101 / 160) ∧
    -Real.log (101 / 160) ≤ (460053299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 261)) (n := 12)
    (lo := (230026649 / 500000000)) (hi := (460053299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 101) = 1/(101 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-460053299 / 1000000000) (-230026649 / 500000000) (Real.log (101 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55379531 / 100000000) ≤ -Real.log (1280 / 2227) ∧
    -Real.log (1280 / 2227) ≤ (553795311 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 3507)) (n := 12)
    (lo := (55379531 / 100000000)) (hi := (553795311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2227 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2227 / 1280) = 1/(1280 / 2227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55379531 / 100000000) (553795311 / 1000000000) (Real.log (2227 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2227 / 1280) = -Real.log (1280 / 2227) := by
    rw [show ((2227 / 1280) : ℝ) = ((1280 / 2227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (673236433 / 500000000) ≤ -Real.log (333 / 1280) ∧
    -Real.log (333 / 1280) ≤ (336618217 / 250000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 333) = 1/(333 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-336618217 / 250000000) (-673236433 / 500000000) (Real.log (333 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (276223649 / 500000000) ≤ -Real.log (80 / 139) ∧
    -Real.log (80 / 139) ≤ (552447299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 219)) (n := 12)
    (lo := (276223649 / 500000000)) (hi := (552447299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 80) = 1/(80 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (276223649 / 500000000) (552447299 / 1000000000) (Real.log (139 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (139 / 80) = -Real.log (80 / 139) := by
    rw [show ((139 / 80) : ℝ) = ((80 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (334376049 / 250000000) ≤ -Real.log (21 / 80) ∧
    -Real.log (21 / 80) ≤ (668752099 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 21) = 1/(21 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-668752099 / 500000000) (-334376049 / 250000000) (Real.log (21 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (429974289 / 1000000000) ≤ -Real.log (500000 / 768609) ∧
    -Real.log (500000 / 768609) ≤ (42997429 / 100000000) := by
  have h := checkLog_sound (w := (268609 / 1268609)) (n := 12)
    (lo := (429974289 / 1000000000)) (hi := (42997429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768609 / 500000) = 1/(500000 / 768609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (429974289 / 1000000000) (42997429 / 100000000) (Real.log (768609 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (768609 / 500000) = -Real.log (500000 / 768609) := by
    rw [show ((768609 / 500000) : ℝ) = ((500000 / 768609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (770499177 / 1000000000) ≤ -Real.log (231391 / 500000) ∧
    -Real.log (231391 / 500000) ≤ (770499179 / 1000000000) := by
  have h := checkLog_sound (w := (18609 / 481391)) (n := 12)
    (lo := (77351997 / 1000000000)) (hi := (38675999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231391) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 231391) = 1/(231391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-770499179 / 1000000000) (-770499177 / 1000000000) (Real.log (231391 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (431175089 / 1000000000) ≤ -Real.log (200000 / 307813) ∧
    -Real.log (200000 / 307813) ≤ (43117509 / 100000000) := by
  have h := checkLog_sound (w := (107813 / 507813)) (n := 12)
    (lo := (431175089 / 1000000000)) (hi := (43117509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307813 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307813 / 200000) = 1/(200000 / 307813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (431175089 / 1000000000) (43117509 / 100000000) (Real.log (307813 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (307813 / 200000) = -Real.log (200000 / 307813) := by
    rw [show ((307813 / 200000) : ℝ) = ((200000 / 307813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (774498243 / 1000000000) ≤ -Real.log (92187 / 200000) ∧
    -Real.log (92187 / 200000) ≤ (154899649 / 200000000) := by
  have h := checkLog_sound (w := (7813 / 192187)) (n := 12)
    (lo := (81351063 / 1000000000)) (hi := (10168883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 92187) = 1/(92187 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154899649 / 200000000) (-774498243 / 1000000000) (Real.log (92187 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (345487901 / 1000000000) ≤ -Real.log (1000000 / 1412679) ∧
    -Real.log (1000000 / 1412679) ≤ (172743951 / 500000000) := by
  have h := checkLog_sound (w := (412679 / 2412679)) (n := 12)
    (lo := (345487901 / 1000000000)) (hi := (172743951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412679 / 1000000) = 1/(1000000 / 1412679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (345487901 / 1000000000) (172743951 / 500000000) (Real.log (1412679 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1412679 / 1000000) = -Real.log (1000000 / 1412679) := by
    rw [show ((1412679 / 1000000) : ℝ) = ((1000000 / 1412679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6652297 / 12500000) ≤ -Real.log (587321 / 1000000) ∧
    -Real.log (587321 / 1000000) ≤ (532183761 / 1000000000) := by
  have h := checkLog_sound (w := (412679 / 1587321)) (n := 12)
    (lo := (6652297 / 12500000)) (hi := (532183761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587321) = 1/(587321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-532183761 / 1000000000) (-6652297 / 12500000) (Real.log (587321 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (43333139 / 125000000) ≤ -Real.log (1000000 / 1414343) ∧
    -Real.log (1000000 / 1414343) ≤ (346665113 / 1000000000) := by
  have h := checkLog_sound (w := (414343 / 2414343)) (n := 12)
    (lo := (43333139 / 125000000)) (hi := (346665113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1414343 / 1000000) = 1/(1000000 / 1414343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43333139 / 125000000) (346665113 / 1000000000) (Real.log (1414343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1414343 / 1000000) = -Real.log (1000000 / 1414343) := by
    rw [show ((1414343 / 1000000) : ℝ) = ((1000000 / 1414343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (107004197 / 200000000) ≤ -Real.log (585657 / 1000000) ∧
    -Real.log (585657 / 1000000) ≤ (267510493 / 500000000) := by
  have h := checkLog_sound (w := (414343 / 1585657)) (n := 12)
    (lo := (107004197 / 200000000)) (hi := (267510493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 585657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 585657) = 1/(585657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-267510493 / 500000000) (-107004197 / 200000000) (Real.log (585657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (600236733 / 500000000) ≤ -Real.log (500000000000 / 1660844630949) ∧
    -Real.log (500000000000 / 1660844630949) ≤ (300118367 / 250000000) := by
  have h := checkLog_sound (w := (660844630949 / 2660844630949)) (n := 12)
    (lo := (253663143 / 500000000)) (hi := (507326287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1660844630949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1660844630949 / 1000000000000) = 1/(500000000000 / 1660844630949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (600236733 / 500000000) (300118367 / 250000000) (Real.log (1660844630949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1660844630949 / 500000000000) = -Real.log (500000000000 / 1660844630949) := by
    rw [show ((1660844630949 / 500000000000) : ℝ) = ((500000000000 / 1660844630949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (301418333 / 250000000) ≤ -Real.log (250000000000 / 834751646111) ∧
    -Real.log (250000000000 / 834751646111) ≤ (602836667 / 500000000) := by
  have h := checkLog_sound (w := (334751646111 / 1334751646111)) (n := 12)
    (lo := (64065769 / 125000000)) (hi := (512526153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834751646111 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(834751646111 / 500000000000) = 1/(250000000000 / 834751646111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (301418333 / 250000000) (602836667 / 500000000) (Real.log (834751646111 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (834751646111 / 250000000000) = -Real.log (250000000000 / 834751646111) := by
    rw [show ((834751646111 / 250000000000) : ℝ) = ((250000000000 / 834751646111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (877671661 / 1000000000) ≤ -Real.log (100000000000 / 240529284667) ∧
    -Real.log (100000000000 / 240529284667) ≤ (877671663 / 1000000000) := by
  have h := checkLog_sound (w := (40529284667 / 440529284667)) (n := 12)
    (lo := (184524481 / 1000000000)) (hi := (92262241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240529284667 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(240529284667 / 200000000000) = 1/(100000000000 / 240529284667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (877671661 / 1000000000) (877671663 / 1000000000) (Real.log (240529284667 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (240529284667 / 100000000000) = -Real.log (100000000000 / 240529284667) := by
    rw [show ((240529284667 / 100000000000) : ℝ) = ((100000000000 / 240529284667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55105381 / 62500000) ≤ -Real.log (500000000000 / 1207484073443) ∧
    -Real.log (500000000000 / 1207484073443) ≤ (440843049 / 500000000) := by
  have h := checkLog_sound (w := (207484073443 / 2207484073443)) (n := 12)
    (lo := (47134729 / 250000000)) (hi := (188538917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207484073443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1207484073443 / 1000000000000) = 1/(500000000000 / 1207484073443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55105381 / 62500000) (440843049 / 500000000) (Real.log (1207484073443 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1207484073443 / 500000000000) = -Real.log (500000000000 / 1207484073443) := by
    rw [show ((1207484073443 / 500000000000) : ℝ) = ((500000000000 / 1207484073443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0122

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0123Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0123
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

theorem reflection_log_1_neg : (156948957 / 500000000) ≤ -Real.log (160 / 219) ∧
    -Real.log (160 / 219) ≤ (62779583 / 200000000) := by
  have h := checkLog_sound (w := (59 / 379)) (n := 12)
    (lo := (156948957 / 500000000)) (hi := (62779583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 160) = 1/(160 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156948957 / 500000000) (62779583 / 200000000) (Real.log (219 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (219 / 160) = -Real.log (160 / 219) := by
    rw [show ((219 / 160) : ℝ) = ((160 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230026649 / 500000000) ≤ -Real.log (101 / 160) ∧
    -Real.log (101 / 160) ≤ (460053299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 261)) (n := 12)
    (lo := (230026649 / 500000000)) (hi := (460053299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 101) = 1/(101 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-460053299 / 1000000000) (-230026649 / 500000000) (Real.log (101 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (313041383 / 1000000000) ≤ -Real.log (2560 / 3501) ∧
    -Real.log (2560 / 3501) ≤ (39130173 / 125000000) := by
  have h := checkLog_sound (w := (941 / 6061)) (n := 12)
    (lo := (313041383 / 1000000000)) (hi := (39130173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501 / 2560) = 1/(2560 / 3501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (313041383 / 1000000000) (39130173 / 125000000) (Real.log (3501 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3501 / 2560) = -Real.log (2560 / 3501) := by
    rw [show ((3501 / 2560) : ℝ) = ((2560 / 3501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (458198583 / 1000000000) ≤ -Real.log (1619 / 2560) ∧
    -Real.log (1619 / 2560) ≤ (57274823 / 125000000) := by
  have h := checkLog_sound (w := (941 / 4179)) (n := 12)
    (lo := (458198583 / 1000000000)) (hi := (57274823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1619) = 1/(1619 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57274823 / 125000000) (-458198583 / 1000000000) (Real.log (1619 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (276223649 / 500000000) ≤ -Real.log (80 / 139) ∧
    -Real.log (80 / 139) ≤ (552447299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 219)) (n := 12)
    (lo := (276223649 / 500000000)) (hi := (552447299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 80) = 1/(80 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (276223649 / 500000000) (552447299 / 1000000000) (Real.log (139 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (139 / 80) = -Real.log (80 / 139) := by
    rw [show ((139 / 80) : ℝ) = ((80 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (334376049 / 250000000) ≤ -Real.log (21 / 80) ∧
    -Real.log (21 / 80) ≤ (668752099 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 21) = 1/(21 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-668752099 / 500000000) (-334376049 / 250000000) (Real.log (21 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (275548733 / 500000000) ≤ -Real.log (1280 / 2221) ∧
    -Real.log (1280 / 2221) ≤ (551097467 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 3501)) (n := 12)
    (lo := (275548733 / 500000000)) (hi := (551097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2221 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2221 / 1280) = 1/(1280 / 2221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (275548733 / 500000000) (551097467 / 1000000000) (Real.log (2221 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2221 / 1280) = -Real.log (1280 / 2221) := by
    rw [show ((2221 / 1280) : ℝ) = ((1280 / 2221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (83038453 / 62500000) ≤ -Real.log (339 / 1280) ∧
    -Real.log (339 / 1280) ≤ (5314461 / 4000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 339) = 1/(339 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5314461 / 4000000) (-83038453 / 62500000) (Real.log (339 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (428773999 / 1000000000) ≤ -Real.log (500000 / 767687) ∧
    -Real.log (500000 / 767687) ≤ (214387 / 500000) := by
  have h := checkLog_sound (w := (267687 / 1267687)) (n := 12)
    (lo := (428773999 / 1000000000)) (hi := (214387 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767687 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767687 / 500000) = 1/(500000 / 767687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (428773999 / 1000000000) (214387 / 500000) (Real.log (767687 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (767687 / 500000) = -Real.log (500000 / 767687) := by
    rw [show ((767687 / 500000) : ℝ) = ((500000 / 767687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (766522497 / 1000000000) ≤ -Real.log (232313 / 500000) ∧
    -Real.log (232313 / 500000) ≤ (766522499 / 1000000000) := by
  have h := checkLog_sound (w := (17687 / 482313)) (n := 12)
    (lo := (73375317 / 1000000000)) (hi := (36687659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 232313) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 232313) = 1/(232313 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-766522499 / 1000000000) (-766522497 / 1000000000) (Real.log (232313 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (429974939 / 1000000000) ≤ -Real.log (1000000 / 1537219) ∧
    -Real.log (1000000 / 1537219) ≤ (21498747 / 50000000) := by
  have h := checkLog_sound (w := (537219 / 2537219)) (n := 12)
    (lo := (429974939 / 1000000000)) (hi := (21498747 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1537219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1537219 / 1000000) = 1/(1000000 / 1537219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (429974939 / 1000000000) (21498747 / 50000000) (Real.log (1537219 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1537219 / 1000000) = -Real.log (1000000 / 1537219) := by
    rw [show ((1537219 / 1000000) : ℝ) = ((1000000 / 1537219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (385250669 / 500000000) ≤ -Real.log (462781 / 1000000) ∧
    -Real.log (462781 / 1000000) ≤ (38525067 / 50000000) := by
  have h := checkLog_sound (w := (37219 / 962781)) (n := 12)
    (lo := (38677079 / 500000000)) (hi := (77354159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 462781) = 1/(462781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38525067 / 50000000) (-385250669 / 500000000) (Real.log (462781 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (43039283 / 125000000) ≤ -Real.log (500000 / 705511) ∧
    -Real.log (500000 / 705511) ≤ (68862853 / 200000000) := by
  have h := checkLog_sound (w := (205511 / 1205511)) (n := 12)
    (lo := (43039283 / 125000000)) (hi := (68862853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705511 / 500000) = 1/(500000 / 705511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (43039283 / 125000000) (68862853 / 200000000) (Real.log (705511 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (705511 / 500000) = -Real.log (500000 / 705511) := by
    rw [show ((705511 / 500000) : ℝ) = ((500000 / 705511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (529366447 / 1000000000) ≤ -Real.log (294489 / 500000) ∧
    -Real.log (294489 / 500000) ≤ (33085403 / 62500000) := by
  have h := checkLog_sound (w := (205511 / 794489)) (n := 12)
    (lo := (529366447 / 1000000000)) (hi := (33085403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 294489) = 1/(294489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-33085403 / 62500000) (-529366447 / 1000000000) (Real.log (294489 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (345489317 / 1000000000) ≤ -Real.log (1000000 / 1412681) ∧
    -Real.log (1000000 / 1412681) ≤ (172744659 / 500000000) := by
  have h := checkLog_sound (w := (412681 / 2412681)) (n := 12)
    (lo := (345489317 / 1000000000)) (hi := (172744659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412681 / 1000000) = 1/(1000000 / 1412681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (345489317 / 1000000000) (172744659 / 500000000) (Real.log (1412681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1412681 / 1000000) = -Real.log (1000000 / 1412681) := by
    rw [show ((1412681 / 1000000) : ℝ) = ((1000000 / 1412681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106437433 / 200000000) ≤ -Real.log (587319 / 1000000) ∧
    -Real.log (587319 / 1000000) ≤ (266093583 / 500000000) := by
  have h := checkLog_sound (w := (412681 / 1587319)) (n := 12)
    (lo := (106437433 / 200000000)) (hi := (266093583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587319) = 1/(587319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-266093583 / 500000000) (-106437433 / 200000000) (Real.log (587319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1195296497 / 1000000000) ≤ -Real.log (500000000000 / 1652268706443) ∧
    -Real.log (500000000000 / 1652268706443) ≤ (1195296499 / 1000000000) := by
  have h := checkLog_sound (w := (652268706443 / 2652268706443)) (n := 12)
    (lo := (502149317 / 1000000000)) (hi := (251074659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652268706443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652268706443 / 1000000000000) = 1/(500000000000 / 1652268706443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1195296497 / 1000000000) (1195296499 / 1000000000) (Real.log (1652268706443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1652268706443 / 500000000000) = -Real.log (500000000000 / 1652268706443) := by
    rw [show ((1652268706443 / 500000000000) : ℝ) = ((500000000000 / 1652268706443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (600238139 / 500000000) ≤ -Real.log (500000000000 / 1660849300209) ∧
    -Real.log (500000000000 / 1660849300209) ≤ (30011907 / 25000000) := by
  have h := checkLog_sound (w := (660849300209 / 2660849300209)) (n := 12)
    (lo := (253664549 / 500000000)) (hi := (507329099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1660849300209 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1660849300209 / 1000000000000) = 1/(500000000000 / 1660849300209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (600238139 / 500000000) (30011907 / 25000000) (Real.log (1660849300209 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1660849300209 / 500000000000) = -Real.log (500000000000 / 1660849300209) := by
    rw [show ((1660849300209 / 500000000000) : ℝ) = ((500000000000 / 1660849300209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (873680711 / 1000000000) ≤ -Real.log (125000000000 / 299464071663) ∧
    -Real.log (125000000000 / 299464071663) ≤ (873680713 / 1000000000) := by
  have h := checkLog_sound (w := (49464071663 / 549464071663)) (n := 12)
    (lo := (180533531 / 1000000000)) (hi := (45133383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299464071663 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(299464071663 / 250000000000) = 1/(125000000000 / 299464071663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (873680711 / 1000000000) (873680713 / 1000000000) (Real.log (299464071663 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (299464071663 / 125000000000) = -Real.log (125000000000 / 299464071663) := by
    rw [show ((299464071663 / 125000000000) : ℝ) = ((125000000000 / 299464071663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (438838241 / 500000000) ≤ -Real.log (250000000000 / 601326110683) ∧
    -Real.log (250000000000 / 601326110683) ≤ (219419121 / 250000000) := by
  have h := checkLog_sound (w := (101326110683 / 1101326110683)) (n := 12)
    (lo := (92264651 / 500000000)) (hi := (184529303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601326110683 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(601326110683 / 500000000000) = 1/(250000000000 / 601326110683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (438838241 / 500000000) (219419121 / 250000000) (Real.log (601326110683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (601326110683 / 250000000000) = -Real.log (250000000000 / 601326110683) := by
    rw [show ((601326110683 / 250000000000) : ℝ) = ((250000000000 / 601326110683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0123

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0124Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0124
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

theorem reflection_log_1_neg : (313041383 / 1000000000) ≤ -Real.log (2560 / 3501) ∧
    -Real.log (2560 / 3501) ≤ (39130173 / 125000000) := by
  have h := checkLog_sound (w := (941 / 6061)) (n := 12)
    (lo := (313041383 / 1000000000)) (hi := (39130173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501 / 2560) = 1/(2560 / 3501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (313041383 / 1000000000) (39130173 / 125000000) (Real.log (3501 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3501 / 2560) = -Real.log (2560 / 3501) := by
    rw [show ((3501 / 2560) : ℝ) = ((2560 / 3501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (458198583 / 1000000000) ≤ -Real.log (1619 / 2560) ∧
    -Real.log (1619 / 2560) ≤ (57274823 / 125000000) := by
  have h := checkLog_sound (w := (941 / 4179)) (n := 12)
    (lo := (458198583 / 1000000000)) (hi := (57274823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1619) = 1/(1619 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57274823 / 125000000) (-458198583 / 1000000000) (Real.log (1619 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156092059 / 500000000) ≤ -Real.log (1280 / 1749) ∧
    -Real.log (1280 / 1749) ≤ (312184119 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 3029)) (n := 12)
    (lo := (156092059 / 500000000)) (hi := (312184119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1280) = 1/(1280 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156092059 / 500000000) (312184119 / 1000000000) (Real.log (1749 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1749 / 1280) = -Real.log (1280 / 1749) := by
    rw [show ((1749 / 1280) : ℝ) = ((1280 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (228173651 / 500000000) ≤ -Real.log (811 / 1280) ∧
    -Real.log (811 / 1280) ≤ (456347303 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2091)) (n := 12)
    (lo := (228173651 / 500000000)) (hi := (456347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 811) = 1/(811 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-456347303 / 1000000000) (-228173651 / 500000000) (Real.log (811 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (275548733 / 500000000) ≤ -Real.log (1280 / 2221) ∧
    -Real.log (1280 / 2221) ≤ (551097467 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 3501)) (n := 12)
    (lo := (275548733 / 500000000)) (hi := (551097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2221 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2221 / 1280) = 1/(1280 / 2221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (275548733 / 500000000) (551097467 / 1000000000) (Real.log (2221 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2221 / 1280) = -Real.log (1280 / 2221) := by
    rw [show ((2221 / 1280) : ℝ) = ((1280 / 2221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (83038453 / 62500000) ≤ -Real.log (339 / 1280) ∧
    -Real.log (339 / 1280) ≤ (5314461 / 4000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 339) = 1/(339 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5314461 / 4000000) (-83038453 / 62500000) (Real.log (339 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54974581 / 100000000) ≤ -Real.log (640 / 1109) ∧
    -Real.log (640 / 1109) ≤ (549745811 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1749)) (n := 12)
    (lo := (54974581 / 100000000)) (hi := (549745811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109 / 640) = 1/(640 / 1109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54974581 / 100000000) (549745811 / 1000000000) (Real.log (1109 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1109 / 640) = -Real.log (640 / 1109) := by
    rw [show ((1109 / 640) : ℝ) = ((640 / 1109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1319804619 / 1000000000) ≤ -Real.log (171 / 640) ∧
    -Real.log (171 / 640) ≤ (1319804621 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 171) = 1/(171 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1319804621 / 1000000000) (-1319804619 / 1000000000) (Real.log (171 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (427573571 / 1000000000) ≤ -Real.log (250000 / 383383) ∧
    -Real.log (250000 / 383383) ≤ (106893393 / 250000000) := by
  have h := checkLog_sound (w := (133383 / 633383)) (n := 12)
    (lo := (427573571 / 1000000000)) (hi := (106893393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383383 / 250000) = 1/(250000 / 383383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (427573571 / 1000000000) (106893393 / 250000000) (Real.log (383383 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (383383 / 250000) = -Real.log (250000 / 383383) := by
    rw [show ((383383 / 250000) : ℝ) = ((250000 / 383383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23830183 / 31250000) ≤ -Real.log (116617 / 250000) ∧
    -Real.log (116617 / 250000) ≤ (381282929 / 500000000) := by
  have h := checkLog_sound (w := (8383 / 241617)) (n := 12)
    (lo := (17354669 / 250000000)) (hi := (69418677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 116617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 116617) = 1/(116617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-381282929 / 500000000) (-23830183 / 31250000) (Real.log (116617 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8575493 / 20000000) ≤ -Real.log (8000 / 12283) ∧
    -Real.log (8000 / 12283) ≤ (428774651 / 1000000000) := by
  have h := checkLog_sound (w := (4283 / 20283)) (n := 12)
    (lo := (8575493 / 20000000)) (hi := (428774651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12283 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12283 / 8000) = 1/(8000 / 12283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8575493 / 20000000) (428774651 / 1000000000) (Real.log (12283 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (12283 / 8000) = -Real.log (8000 / 12283) := by
    rw [show ((12283 / 8000) : ℝ) = ((8000 / 12283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (766524649 / 1000000000) ≤ -Real.log (3717 / 8000) ∧
    -Real.log (3717 / 8000) ≤ (766524651 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 7717)) (n := 12)
    (lo := (73377469 / 1000000000)) (hi := (7337747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3717) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 3717) = 1/(3717 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-766524651 / 1000000000) (-766524649 / 1000000000) (Real.log (3717 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171571043 / 500000000) ≤ -Real.log (1000000 / 1409369) ∧
    -Real.log (1000000 / 1409369) ≤ (343142087 / 1000000000) := by
  have h := checkLog_sound (w := (409369 / 2409369)) (n := 12)
    (lo := (171571043 / 500000000)) (hi := (343142087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409369 / 1000000) = 1/(1000000 / 1409369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171571043 / 500000000) (343142087 / 1000000000) (Real.log (1409369 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1409369 / 1000000) = -Real.log (1000000 / 1409369) := by
    rw [show ((1409369 / 1000000) : ℝ) = ((1000000 / 1409369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263281911 / 500000000) ≤ -Real.log (590631 / 1000000) ∧
    -Real.log (590631 / 1000000) ≤ (526563823 / 1000000000) := by
  have h := checkLog_sound (w := (409369 / 1590631)) (n := 12)
    (lo := (263281911 / 500000000)) (hi := (526563823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590631) = 1/(590631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-526563823 / 1000000000) (-263281911 / 500000000) (Real.log (590631 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (344314973 / 1000000000) ≤ -Real.log (1000000 / 1411023) ∧
    -Real.log (1000000 / 1411023) ≤ (172157487 / 500000000) := by
  have h := checkLog_sound (w := (411023 / 2411023)) (n := 12)
    (lo := (344314973 / 1000000000)) (hi := (172157487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411023 / 1000000) = 1/(1000000 / 1411023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (344314973 / 1000000000) (172157487 / 500000000) (Real.log (1411023 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1411023 / 1000000) = -Real.log (1000000 / 1411023) := by
    rw [show ((1411023 / 1000000) : ℝ) = ((1000000 / 1411023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (105873629 / 200000000) ≤ -Real.log (588977 / 1000000) ∧
    -Real.log (588977 / 1000000) ≤ (264684073 / 500000000) := by
  have h := checkLog_sound (w := (411023 / 1588977)) (n := 12)
    (lo := (105873629 / 200000000)) (hi := (264684073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 588977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 588977) = 1/(588977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-264684073 / 500000000) (-105873629 / 200000000) (Real.log (588977 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (297534857 / 250000000) ≤ -Real.log (125000000000 / 410942444069) ∧
    -Real.log (125000000000 / 410942444069) ≤ (119013943 / 100000000) := by
  have h := checkLog_sound (w := (160942444069 / 660942444069)) (n := 12)
    (lo := (62124031 / 125000000)) (hi := (496992249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410942444069 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(410942444069 / 250000000000) = 1/(125000000000 / 410942444069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (297534857 / 250000000) (119013943 / 100000000) (Real.log (410942444069 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (410942444069 / 125000000000) = -Real.log (125000000000 / 410942444069) := by
    rw [show ((410942444069 / 125000000000) : ℝ) = ((125000000000 / 410942444069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11952993 / 10000000) ≤ -Real.log (100000000000 / 330454667743) ∧
    -Real.log (100000000000 / 330454667743) ≤ (597649651 / 500000000) := by
  have h := checkLog_sound (w := (130454667743 / 530454667743)) (n := 12)
    (lo := (12553803 / 25000000)) (hi := (502152121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330454667743 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330454667743 / 200000000000) = 1/(100000000000 / 330454667743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11952993 / 10000000) (597649651 / 500000000) (Real.log (330454667743 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330454667743 / 100000000000) = -Real.log (100000000000 / 330454667743) := by
    rw [show ((330454667743 / 100000000000) : ℝ) = ((100000000000 / 330454667743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (869705907 / 1000000000) ≤ -Real.log (50000000000 / 119310449333) ∧
    -Real.log (50000000000 / 119310449333) ≤ (869705909 / 1000000000) := by
  have h := checkLog_sound (w := (19310449333 / 219310449333)) (n := 12)
    (lo := (176558727 / 1000000000)) (hi := (22069841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119310449333 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119310449333 / 100000000000) = 1/(50000000000 / 119310449333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (869705907 / 1000000000) (869705909 / 1000000000) (Real.log (119310449333 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (119310449333 / 50000000000) = -Real.log (50000000000 / 119310449333) := by
    rw [show ((119310449333 / 50000000000) : ℝ) = ((50000000000 / 119310449333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (436841559 / 500000000) ≤ -Real.log (250000000000 / 598929584687) ∧
    -Real.log (250000000000 / 598929584687) ≤ (10921039 / 12500000) := by
  have h := checkLog_sound (w := (98929584687 / 1098929584687)) (n := 12)
    (lo := (90267969 / 500000000)) (hi := (180535939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598929584687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(598929584687 / 500000000000) = 1/(250000000000 / 598929584687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (436841559 / 500000000) (10921039 / 12500000) (Real.log (598929584687 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (598929584687 / 250000000000) = -Real.log (250000000000 / 598929584687) := by
    rw [show ((598929584687 / 250000000000) : ℝ) = ((250000000000 / 598929584687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0124

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0125Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0125
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

theorem reflection_log_1_neg : (156092059 / 500000000) ≤ -Real.log (1280 / 1749) ∧
    -Real.log (1280 / 1749) ≤ (312184119 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 3029)) (n := 12)
    (lo := (156092059 / 500000000)) (hi := (312184119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1280) = 1/(1280 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156092059 / 500000000) (312184119 / 1000000000) (Real.log (1749 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1749 / 1280) = -Real.log (1280 / 1749) := by
    rw [show ((1749 / 1280) : ℝ) = ((1280 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (228173651 / 500000000) ≤ -Real.log (811 / 1280) ∧
    -Real.log (811 / 1280) ≤ (456347303 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2091)) (n := 12)
    (lo := (228173651 / 500000000)) (hi := (456347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 811) = 1/(811 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-456347303 / 1000000000) (-228173651 / 500000000) (Real.log (811 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311326117 / 1000000000) ≤ -Real.log (512 / 699) ∧
    -Real.log (512 / 699) ≤ (155663059 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1211)) (n := 12)
    (lo := (311326117 / 1000000000)) (hi := (155663059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 512) = 1/(512 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311326117 / 1000000000) (155663059 / 500000000) (Real.log (699 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (699 / 512) = -Real.log (512 / 699) := by
    rw [show ((699 / 512) : ℝ) = ((512 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227249721 / 500000000) ≤ -Real.log (325 / 512) ∧
    -Real.log (325 / 512) ≤ (454499443 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 837)) (n := 12)
    (lo := (227249721 / 500000000)) (hi := (454499443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 325) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 325) = 1/(325 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-454499443 / 1000000000) (-227249721 / 500000000) (Real.log (325 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (54974581 / 100000000) ≤ -Real.log (640 / 1109) ∧
    -Real.log (640 / 1109) ≤ (549745811 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1749)) (n := 12)
    (lo := (54974581 / 100000000)) (hi := (549745811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109 / 640) = 1/(640 / 1109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (54974581 / 100000000) (549745811 / 1000000000) (Real.log (1109 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1109 / 640) = -Real.log (640 / 1109) := by
    rw [show ((1109 / 640) : ℝ) = ((640 / 1109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1319804619 / 1000000000) ≤ -Real.log (171 / 640) ∧
    -Real.log (171 / 640) ≤ (1319804621 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 171) = 1/(171 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1319804621 / 1000000000) (-1319804619 / 1000000000) (Real.log (171 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21935693 / 40000000) ≤ -Real.log (256 / 443) ∧
    -Real.log (256 / 443) ≤ (274196163 / 500000000) := by
  have h := checkLog_sound (w := (187 / 699)) (n := 12)
    (lo := (21935693 / 40000000)) (hi := (274196163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443 / 256) = 1/(256 / 443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21935693 / 40000000) (274196163 / 500000000) (Real.log (443 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (443 / 256) = -Real.log (256 / 443) := by
    rw [show ((443 / 256) : ℝ) = ((256 / 443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311070939 / 1000000000) ≤ -Real.log (69 / 256) ∧
    -Real.log (69 / 256) ≤ (1311070941 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 69) = 1/(69 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311070941 / 1000000000) (-1311070939 / 1000000000) (Real.log (69 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (213186503 / 500000000) ≤ -Real.log (250000 / 382923) ∧
    -Real.log (250000 / 382923) ≤ (426373007 / 1000000000) := by
  have h := checkLog_sound (w := (132923 / 632923)) (n := 12)
    (lo := (213186503 / 500000000)) (hi := (426373007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382923 / 250000) = 1/(250000 / 382923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (213186503 / 500000000) (426373007 / 1000000000) (Real.log (382923 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (382923 / 250000) = -Real.log (250000 / 382923) := by
    rw [show ((382923 / 250000) : ℝ) = ((250000 / 382923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (758629079 / 1000000000) ≤ -Real.log (117077 / 250000) ∧
    -Real.log (117077 / 250000) ≤ (758629081 / 1000000000) := by
  have h := checkLog_sound (w := (7923 / 242077)) (n := 12)
    (lo := (65481899 / 1000000000)) (hi := (654819 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 117077) = 1/(117077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-758629081 / 1000000000) (-758629079 / 1000000000) (Real.log (117077 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (427574223 / 1000000000) ≤ -Real.log (1000000 / 1533533) ∧
    -Real.log (1000000 / 1533533) ≤ (26723389 / 62500000) := by
  have h := checkLog_sound (w := (533533 / 2533533)) (n := 12)
    (lo := (427574223 / 1000000000)) (hi := (26723389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533533 / 1000000) = 1/(1000000 / 1533533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (427574223 / 1000000000) (26723389 / 62500000) (Real.log (1533533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1533533 / 1000000) = -Real.log (1000000 / 1533533) := by
    rw [show ((1533533 / 1000000) : ℝ) = ((1000000 / 1533533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95321 / 125000) ≤ -Real.log (466467 / 1000000) ∧
    -Real.log (466467 / 1000000) ≤ (381284001 / 500000000) := by
  have h := checkLog_sound (w := (33533 / 966467)) (n := 12)
    (lo := (3471041 / 50000000)) (hi := (69420821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 466467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 466467) = 1/(466467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-381284001 / 500000000) (-95321 / 125000) (Real.log (466467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85493021 / 250000000) ≤ -Real.log (1000000 / 1407721) ∧
    -Real.log (1000000 / 1407721) ≤ (68394417 / 200000000) := by
  have h := checkLog_sound (w := (407721 / 2407721)) (n := 12)
    (lo := (85493021 / 250000000)) (hi := (68394417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407721 / 1000000) = 1/(1000000 / 1407721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85493021 / 250000000) (68394417 / 200000000) (Real.log (1407721 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1407721 / 1000000) = -Real.log (1000000 / 1407721) := by
    rw [show ((1407721 / 1000000) : ℝ) = ((1000000 / 1407721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (523777471 / 1000000000) ≤ -Real.log (592279 / 1000000) ∧
    -Real.log (592279 / 1000000) ≤ (8184023 / 15625000) := by
  have h := checkLog_sound (w := (407721 / 1592279)) (n := 12)
    (lo := (523777471 / 1000000000)) (hi := (8184023 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 592279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 592279) = 1/(592279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8184023 / 15625000) (-523777471 / 1000000000) (Real.log (592279 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85785699 / 250000000) ≤ -Real.log (100000 / 140937) ∧
    -Real.log (100000 / 140937) ≤ (343142797 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 240937)) (n := 12)
    (lo := (85785699 / 250000000)) (hi := (343142797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140937 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140937 / 100000) = 1/(100000 / 140937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85785699 / 250000000) (343142797 / 1000000000) (Real.log (140937 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (140937 / 100000) = -Real.log (100000 / 140937) := by
    rw [show ((140937 / 100000) : ℝ) = ((100000 / 140937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (105313103 / 200000000) ≤ -Real.log (59063 / 100000) ∧
    -Real.log (59063 / 100000) ≤ (131641379 / 250000000) := by
  have h := checkLog_sound (w := (40937 / 159063)) (n := 12)
    (lo := (105313103 / 200000000)) (hi := (131641379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 59063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 59063) = 1/(59063 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-131641379 / 250000000) (-105313103 / 200000000) (Real.log (59063 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (592501043 / 500000000) ≤ -Real.log (50000000000 / 163534682303) ∧
    -Real.log (50000000000 / 163534682303) ≤ (148125261 / 125000000) := by
  have h := checkLog_sound (w := (63534682303 / 263534682303)) (n := 12)
    (lo := (245927453 / 500000000)) (hi := (491854907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163534682303 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(163534682303 / 100000000000) = 1/(50000000000 / 163534682303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (592501043 / 500000000) (148125261 / 125000000) (Real.log (163534682303 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (163534682303 / 50000000000) = -Real.log (50000000000 / 163534682303) := by
    rw [show ((163534682303 / 50000000000) : ℝ) = ((50000000000 / 163534682303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1190142223 / 1000000000) ≤ -Real.log (100000000000 / 328754874407) ∧
    -Real.log (100000000000 / 328754874407) ≤ (47605689 / 40000000) := by
  have h := checkLog_sound (w := (128754874407 / 528754874407)) (n := 12)
    (lo := (496995043 / 1000000000)) (hi := (124248761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328754874407 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328754874407 / 200000000000) = 1/(100000000000 / 328754874407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1190142223 / 1000000000) (47605689 / 40000000) (Real.log (328754874407 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (328754874407 / 100000000000) = -Real.log (100000000000 / 328754874407) := by
    rw [show ((328754874407 / 100000000000) : ℝ) = ((100000000000 / 328754874407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (173149911 / 200000000) ≤ -Real.log (250000000000 / 594196738361) ∧
    -Real.log (250000000000 / 594196738361) ≤ (865749557 / 1000000000) := by
  have h := checkLog_sound (w := (94196738361 / 1094196738361)) (n := 12)
    (lo := (1380819 / 8000000)) (hi := (21575297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594196738361 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(594196738361 / 500000000000) = 1/(250000000000 / 594196738361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (173149911 / 200000000) (865749557 / 1000000000) (Real.log (594196738361 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (594196738361 / 250000000000) = -Real.log (250000000000 / 594196738361) := by
    rw [show ((594196738361 / 250000000000) : ℝ) = ((250000000000 / 594196738361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (86970831 / 100000000) ≤ -Real.log (250000000000 / 596553679969) ∧
    -Real.log (250000000000 / 596553679969) ≤ (108713539 / 125000000) := by
  have h := checkLog_sound (w := (96553679969 / 1096553679969)) (n := 12)
    (lo := (17656113 / 100000000)) (hi := (176561131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596553679969 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(596553679969 / 500000000000) = 1/(250000000000 / 596553679969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (86970831 / 100000000) (108713539 / 125000000) (Real.log (596553679969 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (596553679969 / 250000000000) = -Real.log (250000000000 / 596553679969) := by
    rw [show ((596553679969 / 250000000000) : ℝ) = ((250000000000 / 596553679969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0125

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0126Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0126
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

theorem reflection_log_1_neg : (311326117 / 1000000000) ≤ -Real.log (512 / 699) ∧
    -Real.log (512 / 699) ≤ (155663059 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1211)) (n := 12)
    (lo := (311326117 / 1000000000)) (hi := (155663059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 512) = 1/(512 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311326117 / 1000000000) (155663059 / 500000000) (Real.log (699 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (699 / 512) = -Real.log (512 / 699) := by
    rw [show ((699 / 512) : ℝ) = ((512 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227249721 / 500000000) ≤ -Real.log (325 / 512) ∧
    -Real.log (325 / 512) ≤ (454499443 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 837)) (n := 12)
    (lo := (227249721 / 500000000)) (hi := (454499443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 325) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 325) = 1/(325 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-454499443 / 1000000000) (-227249721 / 500000000) (Real.log (325 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310467379 / 1000000000) ≤ -Real.log (640 / 873) ∧
    -Real.log (640 / 873) ≤ (15523369 / 50000000) := by
  have h := checkLog_sound (w := (233 / 1513)) (n := 12)
    (lo := (310467379 / 1000000000)) (hi := (15523369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 640) = 1/(640 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310467379 / 1000000000) (15523369 / 50000000) (Real.log (873 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (873 / 640) = -Real.log (640 / 873) := by
    rw [show ((873 / 640) : ℝ) = ((640 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (45265499 / 100000000) ≤ -Real.log (407 / 640) ∧
    -Real.log (407 / 640) ≤ (452654991 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 1047)) (n := 12)
    (lo := (45265499 / 100000000)) (hi := (452654991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 407) = 1/(407 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-452654991 / 1000000000) (-45265499 / 100000000) (Real.log (407 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21935693 / 40000000) ≤ -Real.log (256 / 443) ∧
    -Real.log (256 / 443) ≤ (274196163 / 500000000) := by
  have h := checkLog_sound (w := (187 / 699)) (n := 12)
    (lo := (21935693 / 40000000)) (hi := (274196163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443 / 256) = 1/(256 / 443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21935693 / 40000000) (274196163 / 500000000) (Real.log (443 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (443 / 256) = -Real.log (256 / 443) := by
    rw [show ((443 / 256) : ℝ) = ((256 / 443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311070939 / 1000000000) ≤ -Real.log (69 / 256) ∧
    -Real.log (69 / 256) ≤ (1311070941 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 69) = 1/(69 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311070941 / 1000000000) (-1311070939 / 1000000000) (Real.log (69 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109407401 / 200000000) ≤ -Real.log (320 / 553) ∧
    -Real.log (320 / 553) ≤ (273518503 / 500000000) := by
  have h := checkLog_sound (w := (233 / 873)) (n := 12)
    (lo := (109407401 / 200000000)) (hi := (273518503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(553 / 320) = 1/(320 / 553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109407401 / 200000000) (273518503 / 500000000) (Real.log (553 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (553 / 320) = -Real.log (320 / 553) := by
    rw [show ((553 / 320) : ℝ) = ((320 / 553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325603219 / 250000000) ≤ -Real.log (87 / 320) ∧
    -Real.log (87 / 320) ≤ (651206439 / 500000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 87) = 1/(87 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-651206439 / 500000000) (-325603219 / 250000000) (Real.log (87 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (212586153 / 500000000) ≤ -Real.log (500000 / 764927) ∧
    -Real.log (500000 / 764927) ≤ (425172307 / 1000000000) := by
  have h := checkLog_sound (w := (264927 / 1264927)) (n := 12)
    (lo := (212586153 / 500000000)) (hi := (425172307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764927 / 500000) = 1/(500000 / 764927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (212586153 / 500000000) (425172307 / 1000000000) (Real.log (764927 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (764927 / 500000) = -Real.log (500000 / 764927) := by
    rw [show ((764927 / 500000) : ℝ) = ((500000 / 764927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (754711993 / 1000000000) ≤ -Real.log (235073 / 500000) ∧
    -Real.log (235073 / 500000) ≤ (150942399 / 200000000) := by
  have h := checkLog_sound (w := (14927 / 485073)) (n := 12)
    (lo := (61564813 / 1000000000)) (hi := (30782407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235073) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235073) = 1/(235073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150942399 / 200000000) (-754711993 / 1000000000) (Real.log (235073 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (426373659 / 1000000000) ≤ -Real.log (1000000 / 1531693) ∧
    -Real.log (1000000 / 1531693) ≤ (21318683 / 50000000) := by
  have h := checkLog_sound (w := (531693 / 2531693)) (n := 12)
    (lo := (426373659 / 1000000000)) (hi := (21318683 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1531693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1531693 / 1000000) = 1/(1000000 / 1531693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (426373659 / 1000000000) (21318683 / 50000000) (Real.log (1531693 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1531693 / 1000000) = -Real.log (1000000 / 1531693) := by
    rw [show ((1531693 / 1000000) : ℝ) = ((1000000 / 1531693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (379315607 / 500000000) ≤ -Real.log (468307 / 1000000) ∧
    -Real.log (468307 / 1000000) ≤ (47414451 / 62500000) := by
  have h := checkLog_sound (w := (31693 / 968307)) (n := 12)
    (lo := (32742017 / 500000000)) (hi := (13096807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 468307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 468307) = 1/(468307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-47414451 / 62500000) (-379315607 / 500000000) (Real.log (468307 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (340803557 / 1000000000) ≤ -Real.log (1000000 / 1406077) ∧
    -Real.log (1000000 / 1406077) ≤ (170401779 / 500000000) := by
  have h := checkLog_sound (w := (406077 / 2406077)) (n := 12)
    (lo := (340803557 / 1000000000)) (hi := (170401779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1406077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1406077 / 1000000) = 1/(1000000 / 1406077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (340803557 / 1000000000) (170401779 / 500000000) (Real.log (1406077 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1406077 / 1000000) = -Real.log (1000000 / 1406077) := by
    rw [show ((1406077 / 1000000) : ℝ) = ((1000000 / 1406077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (521005597 / 1000000000) ≤ -Real.log (593923 / 1000000) ∧
    -Real.log (593923 / 1000000) ≤ (260502799 / 500000000) := by
  have h := checkLog_sound (w := (406077 / 1593923)) (n := 12)
    (lo := (521005597 / 1000000000)) (hi := (260502799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 593923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 593923) = 1/(593923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260502799 / 500000000) (-521005597 / 1000000000) (Real.log (593923 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (68394559 / 200000000) ≤ -Real.log (500000 / 703861) ∧
    -Real.log (500000 / 703861) ≤ (85493199 / 250000000) := by
  have h := checkLog_sound (w := (203861 / 1203861)) (n := 12)
    (lo := (68394559 / 200000000)) (hi := (85493199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703861 / 500000) = 1/(500000 / 703861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (68394559 / 200000000) (85493199 / 250000000) (Real.log (703861 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (703861 / 500000) = -Real.log (500000 / 703861) := by
    rw [show ((703861 / 500000) : ℝ) = ((500000 / 703861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (523779159 / 1000000000) ≤ -Real.log (296139 / 500000) ∧
    -Real.log (296139 / 500000) ≤ (13094479 / 25000000) := by
  have h := checkLog_sound (w := (203861 / 796139)) (n := 12)
    (lo := (523779159 / 1000000000)) (hi := (13094479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296139) = 1/(296139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-13094479 / 25000000) (-523779159 / 1000000000) (Real.log (296139 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1179884299 / 1000000000) ≤ -Real.log (250000000000 / 813499423583) ∧
    -Real.log (250000000000 / 813499423583) ≤ (1179884301 / 1000000000) := by
  have h := checkLog_sound (w := (313499423583 / 1313499423583)) (n := 12)
    (lo := (486737119 / 1000000000)) (hi := (3042107 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813499423583 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(813499423583 / 500000000000) = 1/(250000000000 / 813499423583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1179884299 / 1000000000) (1179884301 / 1000000000) (Real.log (813499423583 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (813499423583 / 250000000000) = -Real.log (250000000000 / 813499423583) := by
    rw [show ((813499423583 / 250000000000) : ℝ) = ((250000000000 / 813499423583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (592502437 / 500000000) ≤ -Real.log (500000000000 / 1635351382747) ∧
    -Real.log (500000000000 / 1635351382747) ≤ (296251219 / 250000000) := by
  have h := checkLog_sound (w := (635351382747 / 2635351382747)) (n := 12)
    (lo := (245928847 / 500000000)) (hi := (98371539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1635351382747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1635351382747 / 1000000000000) = 1/(500000000000 / 1635351382747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (592502437 / 500000000) (296251219 / 250000000) (Real.log (1635351382747 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1635351382747 / 500000000000) = -Real.log (500000000000 / 1635351382747) := by
    rw [show ((1635351382747 / 500000000000) : ℝ) = ((500000000000 / 1635351382747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (430904577 / 500000000) ≤ -Real.log (250000000000 / 591859971747) ∧
    -Real.log (250000000000 / 591859971747) ≤ (215452289 / 250000000) := by
  have h := checkLog_sound (w := (91859971747 / 1091859971747)) (n := 12)
    (lo := (84330987 / 500000000)) (hi := (6746479 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591859971747 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(591859971747 / 500000000000) = 1/(250000000000 / 591859971747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (430904577 / 500000000) (215452289 / 250000000) (Real.log (591859971747 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (591859971747 / 250000000000) = -Real.log (250000000000 / 591859971747) := by
    rw [show ((591859971747 / 250000000000) : ℝ) = ((250000000000 / 591859971747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (432875977 / 500000000) ≤ -Real.log (500000000000 / 1188396327401) ∧
    -Real.log (500000000000 / 1188396327401) ≤ (216437989 / 250000000) := by
  have h := checkLog_sound (w := (188396327401 / 2188396327401)) (n := 12)
    (lo := (86302387 / 500000000)) (hi := (6904191 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188396327401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1188396327401 / 1000000000000) = 1/(500000000000 / 1188396327401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (432875977 / 500000000) (216437989 / 250000000) (Real.log (1188396327401 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1188396327401 / 500000000000) = -Real.log (500000000000 / 1188396327401) := by
    rw [show ((1188396327401 / 500000000000) : ℝ) = ((500000000000 / 1188396327401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0126

end


