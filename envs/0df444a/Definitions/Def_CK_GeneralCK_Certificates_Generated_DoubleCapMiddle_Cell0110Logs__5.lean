-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0110Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0110Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:11:00.646719+00:00
-- url     : https://prove2.me/theorems/fdc6d5d2-2383-491f-a301-acd5c24a8714
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0110Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0111Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0110Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0110Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0110Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0110Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0111Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0112Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0113Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0114Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0110Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0110
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

theorem reflection_log_1_neg : (324966567 / 1000000000) ≤ -Real.log (2560 / 3543) ∧
    -Real.log (2560 / 3543) ≤ (40620821 / 125000000) := by
  have h := checkLog_sound (w := (983 / 6103)) (n := 12)
    (lo := (324966567 / 1000000000)) (hi := (40620821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3543 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3543 / 2560) = 1/(2560 / 3543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324966567 / 1000000000) (40620821 / 125000000) (Real.log (3543 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3543 / 2560) = -Real.log (2560 / 3543) := by
    rw [show ((3543 / 2560) : ℝ) = ((2560 / 3543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9689659 / 20000000) ≤ -Real.log (1577 / 2560) ∧
    -Real.log (1577 / 2560) ≤ (484482951 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 4137)) (n := 12)
    (lo := (9689659 / 20000000)) (hi := (484482951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1577) = 1/(1577 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-484482951 / 1000000000) (-9689659 / 20000000) (Real.log (1577 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (81029867 / 250000000) ≤ -Real.log (128 / 177) ∧
    -Real.log (128 / 177) ≤ (324119469 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 305)) (n := 12)
    (lo := (81029867 / 250000000)) (hi := (324119469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 128) = 1/(128 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (81029867 / 250000000) (324119469 / 1000000000) (Real.log (177 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (177 / 128) = -Real.log (128 / 177) := by
    rw [show ((177 / 128) : ℝ) = ((128 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (482582411 / 1000000000) ≤ -Real.log (79 / 128) ∧
    -Real.log (79 / 128) ≤ (120645603 / 250000000) := by
  have h := checkLog_sound (w := (49 / 207)) (n := 12)
    (lo := (482582411 / 1000000000)) (hi := (120645603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 79) = 1/(79 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-120645603 / 250000000) (-482582411 / 1000000000) (Real.log (79 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71228911 / 125000000) ≤ -Real.log (1280 / 2263) ∧
    -Real.log (1280 / 2263) ≤ (569831289 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 3543)) (n := 12)
    (lo := (71228911 / 125000000)) (hi := (569831289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2263 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2263 / 1280) = 1/(1280 / 2263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71228911 / 125000000) (569831289 / 1000000000) (Real.log (2263 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2263 / 1280) = -Real.log (1280 / 2263) := by
    rw [show ((2263 / 1280) : ℝ) = ((1280 / 2263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (91305201 / 62500000) ≤ -Real.log (297 / 1280) ∧
    -Real.log (297 / 1280) ≤ (1460883219 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 297) = 1/(297 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1460883219 / 1000000000) (-91305201 / 62500000) (Real.log (297 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113700947 / 200000000) ≤ -Real.log (64 / 113) ∧
    -Real.log (64 / 113) ≤ (17765773 / 31250000) := by
  have h := checkLog_sound (w := (49 / 177)) (n := 12)
    (lo := (113700947 / 200000000)) (hi := (17765773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113 / 64) = 1/(64 / 113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113700947 / 200000000) (17765773 / 31250000) (Real.log (113 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (113 / 64) = -Real.log (64 / 113) := by
    rw [show ((113 / 64) : ℝ) = ((64 / 113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-362708221 / 250000000) (-1450832881 / 1000000000) (Real.log (15 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (444373593 / 1000000000) ≤ -Real.log (1000000 / 1559513) ∧
    -Real.log (1000000 / 1559513) ≤ (222186797 / 500000000) := by
  have h := checkLog_sound (w := (559513 / 2559513)) (n := 12)
    (lo := (444373593 / 1000000000)) (hi := (222186797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1559513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1559513 / 1000000) = 1/(1000000 / 1559513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (444373593 / 1000000000) (222186797 / 500000000) (Real.log (1559513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1559513 / 1000000) = -Real.log (1000000 / 1559513) := by
    rw [show ((1559513 / 1000000) : ℝ) = ((1000000 / 1559513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (163974869 / 200000000) ≤ -Real.log (440487 / 1000000) ∧
    -Real.log (440487 / 1000000) ≤ (819874347 / 1000000000) := by
  have h := checkLog_sound (w := (59513 / 940487)) (n := 12)
    (lo := (25345433 / 200000000)) (hi := (63363583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440487) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 440487) = 1/(440487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-819874347 / 1000000000) (-163974869 / 200000000) (Real.log (440487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3481051 / 7812500) ≤ -Real.log (1000000 / 1561387) ∧
    -Real.log (1000000 / 1561387) ≤ (445574529 / 1000000000) := by
  have h := checkLog_sound (w := (561387 / 2561387)) (n := 12)
    (lo := (3481051 / 7812500)) (hi := (445574529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1561387 / 1000000) = 1/(1000000 / 1561387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3481051 / 7812500) (445574529 / 1000000000) (Real.log (1561387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1561387 / 1000000) = -Real.log (1000000 / 1561387) := by
    rw [show ((1561387 / 1000000) : ℝ) = ((1000000 / 1561387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (824137803 / 1000000000) ≤ -Real.log (438613 / 1000000) ∧
    -Real.log (438613 / 1000000) ≤ (164827561 / 200000000) := by
  have h := checkLog_sound (w := (61387 / 938613)) (n := 12)
    (lo := (130990623 / 1000000000)) (hi := (4093457 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438613) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 438613) = 1/(438613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-164827561 / 200000000) (-824137803 / 1000000000) (Real.log (438613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (359729673 / 1000000000) ≤ -Real.log (500000 / 716471) ∧
    -Real.log (500000 / 716471) ≤ (179864837 / 500000000) := by
  have h := checkLog_sound (w := (216471 / 1216471)) (n := 12)
    (lo := (359729673 / 1000000000)) (hi := (179864837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716471 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716471 / 500000) = 1/(500000 / 716471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (359729673 / 1000000000) (179864837 / 500000000) (Real.log (716471 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (716471 / 500000) = -Real.log (500000 / 716471) := by
    rw [show ((716471 / 500000) : ℝ) = ((500000 / 716471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (567293687 / 1000000000) ≤ -Real.log (283529 / 500000) ∧
    -Real.log (283529 / 500000) ≤ (70911711 / 125000000) := by
  have h := checkLog_sound (w := (216471 / 783529)) (n := 12)
    (lo := (567293687 / 1000000000)) (hi := (70911711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 283529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 283529) = 1/(283529 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-70911711 / 125000000) (-567293687 / 1000000000) (Real.log (283529 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14437227 / 40000000) ≤ -Real.log (125000 / 179333) ∧
    -Real.log (125000 / 179333) ≤ (90232669 / 250000000) := by
  have h := checkLog_sound (w := (54333 / 304333)) (n := 12)
    (lo := (14437227 / 40000000)) (hi := (90232669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179333 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179333 / 125000) = 1/(125000 / 179333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14437227 / 40000000) (90232669 / 250000000) (Real.log (179333 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (179333 / 125000) = -Real.log (125000 / 179333) := by
    rw [show ((179333 / 125000) : ℝ) = ((125000 / 179333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (285167517 / 500000000) ≤ -Real.log (70667 / 125000) ∧
    -Real.log (70667 / 125000) ≤ (114067007 / 200000000) := by
  have h := checkLog_sound (w := (54333 / 195667)) (n := 12)
    (lo := (285167517 / 500000000)) (hi := (114067007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 70667) = 1/(70667 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-114067007 / 200000000) (-285167517 / 500000000) (Real.log (70667 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (632123969 / 500000000) ≤ -Real.log (500000000000 / 1770214557977) ∧
    -Real.log (500000000000 / 1770214557977) ≤ (63212397 / 50000000) := by
  have h := checkLog_sound (w := (770214557977 / 2770214557977)) (n := 12)
    (lo := (285550379 / 500000000)) (hi := (571100759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1770214557977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1770214557977 / 1000000000000) = 1/(500000000000 / 1770214557977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (632123969 / 500000000) (63212397 / 50000000) (Real.log (1770214557977 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1770214557977 / 500000000000) = -Real.log (500000000000 / 1770214557977) := by
    rw [show ((1770214557977 / 500000000000) : ℝ) = ((500000000000 / 1770214557977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1269712331 / 1000000000) ≤ -Real.log (500000000000 / 1779914184031) ∧
    -Real.log (500000000000 / 1779914184031) ≤ (1269712333 / 1000000000) := by
  have h := checkLog_sound (w := (779914184031 / 2779914184031)) (n := 12)
    (lo := (576565151 / 1000000000)) (hi := (18017661 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779914184031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1779914184031 / 1000000000000) = 1/(500000000000 / 1779914184031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1269712331 / 1000000000) (1269712333 / 1000000000) (Real.log (1779914184031 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1779914184031 / 500000000000) = -Real.log (500000000000 / 1779914184031) := by
    rw [show ((1779914184031 / 500000000000) : ℝ) = ((500000000000 / 1779914184031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (724237 / 781250) ≤ -Real.log (25000000000 / 63174401913) ∧
    -Real.log (25000000000 / 63174401913) ≤ (463511681 / 500000000) := by
  have h := checkLog_sound (w := (13174401913 / 113174401913)) (n := 12)
    (lo := (11693809 / 50000000)) (hi := (233876181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63174401913 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63174401913 / 50000000000) = 1/(25000000000 / 63174401913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (724237 / 781250) (463511681 / 500000000) (Real.log (63174401913 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (63174401913 / 25000000000) = -Real.log (25000000000 / 63174401913) := by
    rw [show ((63174401913 / 25000000000) : ℝ) = ((25000000000 / 63174401913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (931265709 / 1000000000) ≤ -Real.log (125000000000 / 317214895213) ∧
    -Real.log (125000000000 / 317214895213) ≤ (931265711 / 1000000000) := by
  have h := checkLog_sound (w := (67214895213 / 567214895213)) (n := 12)
    (lo := (238118529 / 1000000000)) (hi := (23811853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317214895213 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(317214895213 / 250000000000) = 1/(125000000000 / 317214895213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (931265709 / 1000000000) (931265711 / 1000000000) (Real.log (317214895213 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (317214895213 / 125000000000) = -Real.log (125000000000 / 317214895213) := by
    rw [show ((317214895213 / 125000000000) : ℝ) = ((125000000000 / 317214895213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0110

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0111Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0111
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

theorem reflection_log_1_neg : (81029867 / 250000000) ≤ -Real.log (128 / 177) ∧
    -Real.log (128 / 177) ≤ (324119469 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 305)) (n := 12)
    (lo := (81029867 / 250000000)) (hi := (324119469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 128) = 1/(128 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (81029867 / 250000000) (324119469 / 1000000000) (Real.log (177 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (177 / 128) = -Real.log (128 / 177) := by
    rw [show ((177 / 128) : ℝ) = ((128 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (482582411 / 1000000000) ≤ -Real.log (79 / 128) ∧
    -Real.log (79 / 128) ≤ (120645603 / 250000000) := by
  have h := checkLog_sound (w := (49 / 207)) (n := 12)
    (lo := (482582411 / 1000000000)) (hi := (120645603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 79) = 1/(79 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-120645603 / 250000000) (-482582411 / 1000000000) (Real.log (79 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (323271651 / 1000000000) ≤ -Real.log (2560 / 3537) ∧
    -Real.log (2560 / 3537) ≤ (80817913 / 250000000) := by
  have h := checkLog_sound (w := (977 / 6097)) (n := 12)
    (lo := (323271651 / 1000000000)) (hi := (80817913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3537 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3537 / 2560) = 1/(2560 / 3537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (323271651 / 1000000000) (80817913 / 250000000) (Real.log (3537 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3537 / 2560) = -Real.log (2560 / 3537) := by
    rw [show ((3537 / 2560) : ℝ) = ((2560 / 3537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (480685477 / 1000000000) ≤ -Real.log (1583 / 2560) ∧
    -Real.log (1583 / 2560) ≤ (240342739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 4143)) (n := 12)
    (lo := (480685477 / 1000000000)) (hi := (240342739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1583) = 1/(1583 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240342739 / 500000000) (-480685477 / 1000000000) (Real.log (1583 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113700947 / 200000000) ≤ -Real.log (64 / 113) ∧
    -Real.log (64 / 113) ≤ (17765773 / 31250000) := by
  have h := checkLog_sound (w := (49 / 177)) (n := 12)
    (lo := (113700947 / 200000000)) (hi := (17765773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113 / 64) = 1/(64 / 113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113700947 / 200000000) (17765773 / 31250000) (Real.log (113 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (113 / 64) = -Real.log (64 / 113) := by
    rw [show ((113 / 64) : ℝ) = ((64 / 113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-362708221 / 250000000) (-1450832881 / 1000000000) (Real.log (15 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (567176419 / 1000000000) ≤ -Real.log (1280 / 2257) ∧
    -Real.log (1280 / 2257) ≤ (28358821 / 50000000) := by
  have h := checkLog_sound (w := (977 / 3537)) (n := 12)
    (lo := (567176419 / 1000000000)) (hi := (28358821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2257 / 1280) = 1/(1280 / 2257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (567176419 / 1000000000) (28358821 / 50000000) (Real.log (2257 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2257 / 1280) = -Real.log (1280 / 2257) := by
    rw [show ((2257 / 1280) : ℝ) = ((1280 / 2257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28817651 / 20000000) ≤ -Real.log (303 / 1280) ∧
    -Real.log (303 / 1280) ≤ (1440882553 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 303) = 1/(303 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1440882553 / 1000000000) (-28817651 / 20000000) (Real.log (303 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (443173781 / 1000000000) ≤ -Real.log (1000000 / 1557643) ∧
    -Real.log (1000000 / 1557643) ≤ (221586891 / 500000000) := by
  have h := checkLog_sound (w := (557643 / 2557643)) (n := 12)
    (lo := (443173781 / 1000000000)) (hi := (221586891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557643 / 1000000) = 1/(1000000 / 1557643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (443173781 / 1000000000) (221586891 / 500000000) (Real.log (1557643 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1557643 / 1000000) = -Real.log (1000000 / 1557643) := by
    rw [show ((1557643 / 1000000) : ℝ) = ((1000000 / 1557643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81563803 / 100000000) ≤ -Real.log (442357 / 1000000) ∧
    -Real.log (442357 / 1000000) ≤ (50977377 / 62500000) := by
  have h := checkLog_sound (w := (57643 / 942357)) (n := 12)
    (lo := (2449817 / 20000000)) (hi := (122490851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 442357) = 1/(442357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50977377 / 62500000) (-81563803 / 100000000) (Real.log (442357 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (222187117 / 500000000) ≤ -Real.log (500000 / 779757) ∧
    -Real.log (500000 / 779757) ≤ (88874847 / 200000000) := by
  have h := checkLog_sound (w := (279757 / 1279757)) (n := 12)
    (lo := (222187117 / 500000000)) (hi := (88874847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779757 / 500000) = 1/(500000 / 779757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (222187117 / 500000000) (88874847 / 200000000) (Real.log (779757 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (779757 / 500000) = -Real.log (500000 / 779757) := by
    rw [show ((779757 / 500000) : ℝ) = ((500000 / 779757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (163975323 / 200000000) ≤ -Real.log (220243 / 500000) ∧
    -Real.log (220243 / 500000) ≤ (819876617 / 1000000000) := by
  have h := checkLog_sound (w := (29757 / 470243)) (n := 12)
    (lo := (25345887 / 200000000)) (hi := (31682359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220243) = 1/(220243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-819876617 / 1000000000) (-163975323 / 200000000) (Real.log (220243 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (358531419 / 1000000000) ≤ -Real.log (500000 / 715613) ∧
    -Real.log (500000 / 715613) ≤ (17926571 / 50000000) := by
  have h := checkLog_sound (w := (215613 / 1215613)) (n := 12)
    (lo := (358531419 / 1000000000)) (hi := (17926571 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715613 / 500000) = 1/(500000 / 715613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (358531419 / 1000000000) (17926571 / 50000000) (Real.log (715613 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (715613 / 500000) = -Real.log (500000 / 715613) := by
    rw [show ((715613 / 500000) : ℝ) = ((500000 / 715613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (564272111 / 1000000000) ≤ -Real.log (284387 / 500000) ∧
    -Real.log (284387 / 500000) ≤ (35267007 / 62500000) := by
  have h := checkLog_sound (w := (215613 / 784387)) (n := 12)
    (lo := (564272111 / 1000000000)) (hi := (35267007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 284387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 284387) = 1/(284387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-35267007 / 62500000) (-564272111 / 1000000000) (Real.log (284387 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (359730371 / 1000000000) ≤ -Real.log (1000000 / 1432943) ∧
    -Real.log (1000000 / 1432943) ≤ (89932593 / 250000000) := by
  have h := checkLog_sound (w := (432943 / 2432943)) (n := 12)
    (lo := (359730371 / 1000000000)) (hi := (89932593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432943 / 1000000) = 1/(1000000 / 1432943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (359730371 / 1000000000) (89932593 / 250000000) (Real.log (1432943 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1432943 / 1000000) = -Real.log (1000000 / 1432943) := by
    rw [show ((1432943 / 1000000) : ℝ) = ((1000000 / 1432943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (567295451 / 1000000000) ≤ -Real.log (567057 / 1000000) ∧
    -Real.log (567057 / 1000000) ≤ (141823863 / 250000000) := by
  have h := checkLog_sound (w := (432943 / 1567057)) (n := 12)
    (lo := (567295451 / 1000000000)) (hi := (141823863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567057) = 1/(567057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-141823863 / 250000000) (-567295451 / 1000000000) (Real.log (567057 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1258811811 / 1000000000) ≤ -Real.log (500000000000 / 1760617555503) ∧
    -Real.log (500000000000 / 1760617555503) ≤ (1258811813 / 1000000000) := by
  have h := checkLog_sound (w := (760617555503 / 2760617555503)) (n := 12)
    (lo := (565664631 / 1000000000)) (hi := (70708079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1760617555503 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1760617555503 / 1000000000000) = 1/(500000000000 / 1760617555503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1258811811 / 1000000000) (1258811813 / 1000000000) (Real.log (1760617555503 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1760617555503 / 500000000000) = -Real.log (500000000000 / 1760617555503) := by
    rw [show ((1760617555503 / 500000000000) : ℝ) = ((500000000000 / 1760617555503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1264250849 / 1000000000) ≤ -Real.log (62500000000 / 221277463983) ∧
    -Real.log (62500000000 / 221277463983) ≤ (1264250851 / 1000000000) := by
  have h := checkLog_sound (w := (96277463983 / 346277463983)) (n := 12)
    (lo := (571103669 / 1000000000)) (hi := (57110367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221277463983 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221277463983 / 125000000000) = 1/(62500000000 / 221277463983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1264250849 / 1000000000) (1264250851 / 1000000000) (Real.log (221277463983 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (221277463983 / 62500000000) = -Real.log (62500000000 / 221277463983) := by
    rw [show ((221277463983 / 62500000000) : ℝ) = ((62500000000 / 221277463983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92280353 / 100000000) ≤ -Real.log (250000000000 / 629083783717) ∧
    -Real.log (250000000000 / 629083783717) ≤ (230700883 / 250000000) := by
  have h := checkLog_sound (w := (129083783717 / 1129083783717)) (n := 12)
    (lo := (4593127 / 20000000)) (hi := (229656351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629083783717 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629083783717 / 500000000000) = 1/(250000000000 / 629083783717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92280353 / 100000000) (230700883 / 250000000) (Real.log (629083783717 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (629083783717 / 250000000000) = -Real.log (250000000000 / 629083783717) := by
    rw [show ((629083783717 / 250000000000) : ℝ) = ((250000000000 / 629083783717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (463512911 / 500000000) ≤ -Real.log (500000000000 / 1263491148157) ∧
    -Real.log (500000000000 / 1263491148157) ≤ (28969557 / 31250000) := by
  have h := checkLog_sound (w := (263491148157 / 2263491148157)) (n := 12)
    (lo := (116939321 / 500000000)) (hi := (233878643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263491148157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1263491148157 / 1000000000000) = 1/(500000000000 / 1263491148157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (463512911 / 500000000) (28969557 / 31250000) (Real.log (1263491148157 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1263491148157 / 500000000000) = -Real.log (500000000000 / 1263491148157) := by
    rw [show ((1263491148157 / 500000000000) : ℝ) = ((500000000000 / 1263491148157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0111

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0112Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0112
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

theorem reflection_log_1_neg : (323271651 / 1000000000) ≤ -Real.log (2560 / 3537) ∧
    -Real.log (2560 / 3537) ≤ (80817913 / 250000000) := by
  have h := checkLog_sound (w := (977 / 6097)) (n := 12)
    (lo := (323271651 / 1000000000)) (hi := (80817913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3537 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3537 / 2560) = 1/(2560 / 3537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (323271651 / 1000000000) (80817913 / 250000000) (Real.log (3537 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3537 / 2560) = -Real.log (2560 / 3537) := by
    rw [show ((3537 / 2560) : ℝ) = ((2560 / 3537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (480685477 / 1000000000) ≤ -Real.log (1583 / 2560) ∧
    -Real.log (1583 / 2560) ≤ (240342739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 4143)) (n := 12)
    (lo := (480685477 / 1000000000)) (hi := (240342739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1583) = 1/(1583 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240342739 / 500000000) (-480685477 / 1000000000) (Real.log (1583 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64484623 / 200000000) ≤ -Real.log (1280 / 1767) ∧
    -Real.log (1280 / 1767) ≤ (80605779 / 250000000) := by
  have h := checkLog_sound (w := (487 / 3047)) (n := 12)
    (lo := (64484623 / 200000000)) (hi := (80605779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1767 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1767 / 1280) = 1/(1280 / 1767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64484623 / 200000000) (80605779 / 250000000) (Real.log (1767 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1767 / 1280) = -Real.log (1280 / 1767) := by
    rw [show ((1767 / 1280) : ℝ) = ((1280 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95758427 / 200000000) ≤ -Real.log (793 / 1280) ∧
    -Real.log (793 / 1280) ≤ (59849017 / 125000000) := by
  have h := checkLog_sound (w := (487 / 2073)) (n := 12)
    (lo := (95758427 / 200000000)) (hi := (59849017 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 793) = 1/(793 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59849017 / 125000000) (-95758427 / 200000000) (Real.log (793 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (567176419 / 1000000000) ≤ -Real.log (1280 / 2257) ∧
    -Real.log (1280 / 2257) ≤ (28358821 / 50000000) := by
  have h := checkLog_sound (w := (977 / 3537)) (n := 12)
    (lo := (567176419 / 1000000000)) (hi := (28358821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2257 / 1280) = 1/(1280 / 2257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (567176419 / 1000000000) (28358821 / 50000000) (Real.log (2257 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2257 / 1280) = -Real.log (1280 / 2257) := by
    rw [show ((2257 / 1280) : ℝ) = ((1280 / 2257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28817651 / 20000000) ≤ -Real.log (303 / 1280) ∧
    -Real.log (303 / 1280) ≤ (1440882553 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 303) = 1/(303 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1440882553 / 1000000000) (-28817651 / 20000000) (Real.log (303 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (565846337 / 1000000000) ≤ -Real.log (640 / 1127) ∧
    -Real.log (640 / 1127) ≤ (282923169 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1767)) (n := 12)
    (lo := (565846337 / 1000000000)) (hi := (282923169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127 / 640) = 1/(640 / 1127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (565846337 / 1000000000) (282923169 / 500000000) (Real.log (1127 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1127 / 640) = -Real.log (640 / 1127) := by
    rw [show ((1127 / 640) : ℝ) = ((640 / 1127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1431030253 / 1000000000) ≤ -Real.log (153 / 640) ∧
    -Real.log (153 / 640) ≤ (89439391 / 62500000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 153) = 1/(153 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89439391 / 62500000) (-1431030253 / 1000000000) (Real.log (153 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (441973813 / 1000000000) ≤ -Real.log (40000 / 62231) ∧
    -Real.log (40000 / 62231) ≤ (220986907 / 500000000) := by
  have h := checkLog_sound (w := (22231 / 102231)) (n := 12)
    (lo := (441973813 / 1000000000)) (hi := (220986907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62231 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62231 / 40000) = 1/(40000 / 62231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (441973813 / 1000000000) (220986907 / 500000000) (Real.log (62231 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (62231 / 40000) = -Real.log (40000 / 62231) := by
    rw [show ((62231 / 40000) : ℝ) = ((40000 / 62231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (811424087 / 1000000000) ≤ -Real.log (17769 / 40000) ∧
    -Real.log (17769 / 40000) ≤ (811424089 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 37769)) (n := 12)
    (lo := (118276907 / 1000000000)) (hi := (29569227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 17769) = 1/(17769 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-811424089 / 1000000000) (-811424087 / 1000000000) (Real.log (17769 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (443174423 / 1000000000) ≤ -Real.log (250000 / 389411) ∧
    -Real.log (250000 / 389411) ≤ (55396803 / 125000000) := by
  have h := checkLog_sound (w := (139411 / 639411)) (n := 12)
    (lo := (443174423 / 1000000000)) (hi := (55396803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389411 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389411 / 250000) = 1/(250000 / 389411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (443174423 / 1000000000) (55396803 / 125000000) (Real.log (389411 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (389411 / 250000) = -Real.log (250000 / 389411) := by
    rw [show ((389411 / 250000) : ℝ) = ((250000 / 389411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81564029 / 100000000) ≤ -Real.log (110589 / 250000) ∧
    -Real.log (110589 / 250000) ≤ (203910073 / 250000000) := by
  have h := checkLog_sound (w := (14411 / 235589)) (n := 12)
    (lo := (12249311 / 100000000)) (hi := (122493111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110589) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 110589) = 1/(110589 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203910073 / 250000000) (-81564029 / 100000000) (Real.log (110589 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14293409 / 40000000) ≤ -Real.log (200000 / 285903) ∧
    -Real.log (200000 / 285903) ≤ (178667613 / 500000000) := by
  have h := checkLog_sound (w := (85903 / 485903)) (n := 12)
    (lo := (14293409 / 40000000)) (hi := (178667613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285903 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285903 / 200000) = 1/(200000 / 285903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14293409 / 40000000) (178667613 / 500000000) (Real.log (285903 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (285903 / 200000) = -Real.log (200000 / 285903) := by
    rw [show ((285903 / 200000) : ℝ) = ((200000 / 285903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (280634201 / 500000000) ≤ -Real.log (114097 / 200000) ∧
    -Real.log (114097 / 200000) ≤ (561268403 / 1000000000) := by
  have h := checkLog_sound (w := (85903 / 314097)) (n := 12)
    (lo := (280634201 / 500000000)) (hi := (561268403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114097) = 1/(114097 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-561268403 / 1000000000) (-280634201 / 500000000) (Real.log (114097 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (179266059 / 500000000) ≤ -Real.log (1000000 / 1431227) ∧
    -Real.log (1000000 / 1431227) ≤ (358532119 / 1000000000) := by
  have h := checkLog_sound (w := (431227 / 2431227)) (n := 12)
    (lo := (179266059 / 500000000)) (hi := (358532119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1431227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1431227 / 1000000) = 1/(1000000 / 1431227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (179266059 / 500000000) (358532119 / 1000000000) (Real.log (1431227 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1431227 / 1000000) = -Real.log (1000000 / 1431227) := by
    rw [show ((1431227 / 1000000) : ℝ) = ((1000000 / 1431227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (564273869 / 1000000000) ≤ -Real.log (568773 / 1000000) ∧
    -Real.log (568773 / 1000000) ≤ (56427387 / 100000000) := by
  have h := checkLog_sound (w := (431227 / 1568773)) (n := 12)
    (lo := (564273869 / 1000000000)) (hi := (56427387 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 568773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 568773) = 1/(568773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-56427387 / 100000000) (-564273869 / 1000000000) (Real.log (568773 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1253397901 / 1000000000) ≤ -Real.log (62500000000 / 218888935787) ∧
    -Real.log (62500000000 / 218888935787) ≤ (1253397903 / 1000000000) := by
  have h := checkLog_sound (w := (93888935787 / 343888935787)) (n := 12)
    (lo := (560250721 / 1000000000)) (hi := (280125361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218888935787 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218888935787 / 125000000000) = 1/(62500000000 / 218888935787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1253397901 / 1000000000) (1253397903 / 1000000000) (Real.log (218888935787 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (218888935787 / 62500000000) = -Real.log (62500000000 / 218888935787) := by
    rw [show ((218888935787 / 62500000000) : ℝ) = ((62500000000 / 218888935787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1258814713 / 1000000000) ≤ -Real.log (125000000000 / 440155666477) ∧
    -Real.log (125000000000 / 440155666477) ≤ (251762943 / 200000000) := by
  have h := checkLog_sound (w := (190155666477 / 690155666477)) (n := 12)
    (lo := (565667533 / 1000000000)) (hi := (282833767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((440155666477 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(440155666477 / 250000000000) = 1/(125000000000 / 440155666477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1258814713 / 1000000000) (251762943 / 200000000) (Real.log (440155666477 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (440155666477 / 125000000000) = -Real.log (125000000000 / 440155666477) := by
    rw [show ((440155666477 / 125000000000) : ℝ) = ((125000000000 / 440155666477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229650907 / 250000000) ≤ -Real.log (125000000000 / 313223616747) ∧
    -Real.log (125000000000 / 313223616747) ≤ (91860363 / 100000000) := by
  have h := checkLog_sound (w := (63223616747 / 563223616747)) (n := 12)
    (lo := (3522757 / 15625000)) (hi := (225456449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313223616747 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(313223616747 / 250000000000) = 1/(125000000000 / 313223616747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229650907 / 250000000) (91860363 / 100000000) (Real.log (313223616747 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (313223616747 / 125000000000) = -Real.log (125000000000 / 313223616747) := by
    rw [show ((313223616747 / 125000000000) : ℝ) = ((125000000000 / 313223616747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (922805987 / 1000000000) ≤ -Real.log (250000000000 / 629085329297) ∧
    -Real.log (250000000000 / 629085329297) ≤ (922805989 / 1000000000) := by
  have h := checkLog_sound (w := (129085329297 / 1129085329297)) (n := 12)
    (lo := (229658807 / 1000000000)) (hi := (28707351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629085329297 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629085329297 / 500000000000) = 1/(250000000000 / 629085329297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (922805987 / 1000000000) (922805989 / 1000000000) (Real.log (629085329297 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (629085329297 / 250000000000) = -Real.log (250000000000 / 629085329297) := by
    rw [show ((629085329297 / 250000000000) : ℝ) = ((250000000000 / 629085329297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0112

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0113Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0113
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

theorem reflection_log_1_neg : (64484623 / 200000000) ≤ -Real.log (1280 / 1767) ∧
    -Real.log (1280 / 1767) ≤ (80605779 / 250000000) := by
  have h := checkLog_sound (w := (487 / 3047)) (n := 12)
    (lo := (64484623 / 200000000)) (hi := (80605779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1767 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1767 / 1280) = 1/(1280 / 1767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (64484623 / 200000000) (80605779 / 250000000) (Real.log (1767 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1767 / 1280) = -Real.log (1280 / 1767) := by
    rw [show ((1767 / 1280) : ℝ) = ((1280 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95758427 / 200000000) ≤ -Real.log (793 / 1280) ∧
    -Real.log (793 / 1280) ≤ (59849017 / 125000000) := by
  have h := checkLog_sound (w := (487 / 2073)) (n := 12)
    (lo := (95758427 / 200000000)) (hi := (59849017 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 793) = 1/(793 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59849017 / 125000000) (-95758427 / 200000000) (Real.log (793 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (160786929 / 500000000) ≤ -Real.log (2560 / 3531) ∧
    -Real.log (2560 / 3531) ≤ (321573859 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 6091)) (n := 12)
    (lo := (160786929 / 500000000)) (hi := (321573859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3531 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3531 / 2560) = 1/(2560 / 3531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (160786929 / 500000000) (321573859 / 1000000000) (Real.log (3531 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3531 / 2560) = -Real.log (2560 / 3531) := by
    rw [show ((3531 / 2560) : ℝ) = ((2560 / 3531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47690237 / 100000000) ≤ -Real.log (1589 / 2560) ∧
    -Real.log (1589 / 2560) ≤ (476902371 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 4149)) (n := 12)
    (lo := (47690237 / 100000000)) (hi := (476902371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1589) = 1/(1589 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-476902371 / 1000000000) (-47690237 / 100000000) (Real.log (1589 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (565846337 / 1000000000) ≤ -Real.log (640 / 1127) ∧
    -Real.log (640 / 1127) ≤ (282923169 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1767)) (n := 12)
    (lo := (565846337 / 1000000000)) (hi := (282923169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127 / 640) = 1/(640 / 1127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (565846337 / 1000000000) (282923169 / 500000000) (Real.log (1127 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1127 / 640) = -Real.log (640 / 1127) := by
    rw [show ((1127 / 640) : ℝ) = ((640 / 1127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1431030253 / 1000000000) ≤ -Real.log (153 / 640) ∧
    -Real.log (153 / 640) ≤ (89439391 / 62500000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 153) = 1/(153 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-89439391 / 62500000) (-1431030253 / 1000000000) (Real.log (153 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (564514483 / 1000000000) ≤ -Real.log (1280 / 2251) ∧
    -Real.log (1280 / 2251) ≤ (141128621 / 250000000) := by
  have h := checkLog_sound (w := (971 / 3531)) (n := 12)
    (lo := (564514483 / 1000000000)) (hi := (141128621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2251 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2251 / 1280) = 1/(1280 / 2251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (564514483 / 1000000000) (141128621 / 250000000) (Real.log (2251 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2251 / 1280) = -Real.log (1280 / 2251) := by
    rw [show ((2251 / 1280) : ℝ) = ((1280 / 2251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (710637039 / 500000000) ≤ -Real.log (309 / 1280) ∧
    -Real.log (309 / 1280) ≤ (1421274081 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 309) = 1/(309 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1421274081 / 1000000000) (-710637039 / 500000000) (Real.log (309 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (440773691 / 1000000000) ≤ -Real.log (1000000 / 1553909) ∧
    -Real.log (1000000 / 1553909) ≤ (110193423 / 250000000) := by
  have h := checkLog_sound (w := (553909 / 2553909)) (n := 12)
    (lo := (440773691 / 1000000000)) (hi := (110193423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1553909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1553909 / 1000000) = 1/(1000000 / 1553909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (440773691 / 1000000000) (110193423 / 250000000) (Real.log (1553909 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1553909 / 1000000) = -Real.log (1000000 / 1553909) := by
    rw [show ((1553909 / 1000000) : ℝ) = ((1000000 / 1553909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (807232311 / 1000000000) ≤ -Real.log (446091 / 1000000) ∧
    -Real.log (446091 / 1000000) ≤ (807232313 / 1000000000) := by
  have h := checkLog_sound (w := (53909 / 946091)) (n := 12)
    (lo := (114085131 / 1000000000)) (hi := (28521283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 446091) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 446091) = 1/(446091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-807232313 / 1000000000) (-807232311 / 1000000000) (Real.log (446091 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55246807 / 125000000) ≤ -Real.log (15625 / 24309) ∧
    -Real.log (15625 / 24309) ≤ (441974457 / 1000000000) := by
  have h := checkLog_sound (w := (4342 / 19967)) (n := 12)
    (lo := (55246807 / 125000000)) (hi := (441974457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 15625) = 1/(15625 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55246807 / 125000000) (441974457 / 1000000000) (Real.log (24309 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24309 / 15625) = -Real.log (15625 / 24309) := by
    rw [show ((24309 / 15625) : ℝ) = ((15625 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (405713169 / 500000000) ≤ -Real.log (6941 / 15625) ∧
    -Real.log (6941 / 15625) ≤ (40571317 / 50000000) := by
  have h := checkLog_sound (w := (1743 / 29507)) (n := 12)
    (lo := (59139579 / 500000000)) (hi := (118279159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13882) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 13882) = 1/(6941 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-40571317 / 50000000) (-405713169 / 500000000) (Real.log (6941 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (356141801 / 1000000000) ≤ -Real.log (100000 / 142781) ∧
    -Real.log (100000 / 142781) ≤ (178070901 / 500000000) := by
  have h := checkLog_sound (w := (42781 / 242781)) (n := 12)
    (lo := (356141801 / 1000000000)) (hi := (178070901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142781 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142781 / 100000) = 1/(100000 / 142781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (356141801 / 1000000000) (178070901 / 500000000) (Real.log (142781 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (142781 / 100000) = -Real.log (100000 / 142781) := by
    rw [show ((142781 / 100000) : ℝ) = ((100000 / 142781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (279142087 / 500000000) ≤ -Real.log (57219 / 100000) ∧
    -Real.log (57219 / 100000) ≤ (22331367 / 40000000) := by
  have h := checkLog_sound (w := (42781 / 157219)) (n := 12)
    (lo := (279142087 / 500000000)) (hi := (22331367 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57219) = 1/(57219 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-22331367 / 40000000) (-279142087 / 500000000) (Real.log (57219 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14293437 / 40000000) ≤ -Real.log (250000 / 357379) ∧
    -Real.log (250000 / 357379) ≤ (178667963 / 500000000) := by
  have h := checkLog_sound (w := (107379 / 607379)) (n := 12)
    (lo := (14293437 / 40000000)) (hi := (178667963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357379 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357379 / 250000) = 1/(250000 / 357379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14293437 / 40000000) (178667963 / 500000000) (Real.log (357379 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (357379 / 250000) = -Real.log (250000 / 357379) := by
    rw [show ((357379 / 250000) : ℝ) = ((250000 / 357379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (112254031 / 200000000) ≤ -Real.log (142621 / 250000) ∧
    -Real.log (142621 / 250000) ≤ (140317539 / 250000000) := by
  have h := checkLog_sound (w := (107379 / 392621)) (n := 12)
    (lo := (112254031 / 200000000)) (hi := (140317539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142621) = 1/(142621 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-140317539 / 250000000) (-112254031 / 200000000) (Real.log (142621 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1248006003 / 1000000000) ≤ -Real.log (500000000000 / 1741695080151) ∧
    -Real.log (500000000000 / 1741695080151) ≤ (249601201 / 200000000) := by
  have h := checkLog_sound (w := (741695080151 / 2741695080151)) (n := 12)
    (lo := (554858823 / 1000000000)) (hi := (69357353 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741695080151 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1741695080151 / 1000000000000) = 1/(500000000000 / 1741695080151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1248006003 / 1000000000) (249601201 / 200000000) (Real.log (1741695080151 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1741695080151 / 500000000000) = -Real.log (500000000000 / 1741695080151) := by
    rw [show ((1741695080151 / 500000000000) : ℝ) = ((500000000000 / 1741695080151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (250680159 / 200000000) ≤ -Real.log (500000000000 / 1751116553811) ∧
    -Real.log (500000000000 / 1751116553811) ≤ (1253400797 / 1000000000) := by
  have h := checkLog_sound (w := (751116553811 / 2751116553811)) (n := 12)
    (lo := (112050723 / 200000000)) (hi := (35015851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1751116553811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1751116553811 / 1000000000000) = 1/(500000000000 / 1751116553811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (250680159 / 200000000) (1253400797 / 1000000000) (Real.log (1751116553811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1751116553811 / 500000000000) = -Real.log (500000000000 / 1751116553811) := by
    rw [show ((1751116553811 / 500000000000) : ℝ) = ((500000000000 / 1751116553811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (114303247 / 125000000) ≤ -Real.log (62500000000 / 155958903511) ∧
    -Real.log (62500000000 / 155958903511) ≤ (457212989 / 500000000) := by
  have h := checkLog_sound (w := (30958903511 / 280958903511)) (n := 12)
    (lo := (55319699 / 250000000)) (hi := (221278797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155958903511 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(155958903511 / 125000000000) = 1/(62500000000 / 155958903511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (114303247 / 125000000) (457212989 / 500000000) (Real.log (155958903511 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (155958903511 / 62500000000) = -Real.log (62500000000 / 155958903511) := by
    rw [show ((155958903511 / 62500000000) : ℝ) = ((62500000000 / 155958903511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (717661 / 781250) ≤ -Real.log (250000000000 / 626448769817) ∧
    -Real.log (250000000000 / 626448769817) ≤ (459303041 / 500000000) := by
  have h := checkLog_sound (w := (126448769817 / 1126448769817)) (n := 12)
    (lo := (2254589 / 10000000)) (hi := (225458901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626448769817 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(626448769817 / 500000000000) = 1/(250000000000 / 626448769817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (717661 / 781250) (459303041 / 500000000) (Real.log (626448769817 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (626448769817 / 250000000000) = -Real.log (250000000000 / 626448769817) := by
    rw [show ((626448769817 / 250000000000) : ℝ) = ((250000000000 / 626448769817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0113

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0114Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0114
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

theorem reflection_log_1_neg : (160786929 / 500000000) ≤ -Real.log (2560 / 3531) ∧
    -Real.log (2560 / 3531) ≤ (321573859 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 6091)) (n := 12)
    (lo := (160786929 / 500000000)) (hi := (321573859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3531 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3531 / 2560) = 1/(2560 / 3531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (160786929 / 500000000) (321573859 / 1000000000) (Real.log (3531 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3531 / 2560) = -Real.log (2560 / 3531) := by
    rw [show ((3531 / 2560) : ℝ) = ((2560 / 3531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47690237 / 100000000) ≤ -Real.log (1589 / 2560) ∧
    -Real.log (1589 / 2560) ≤ (476902371 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 4149)) (n := 12)
    (lo := (47690237 / 100000000)) (hi := (476902371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1589) = 1/(1589 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-476902371 / 1000000000) (-47690237 / 100000000) (Real.log (1589 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (564514483 / 1000000000) ≤ -Real.log (1280 / 2251) ∧
    -Real.log (1280 / 2251) ≤ (141128621 / 250000000) := by
  have h := checkLog_sound (w := (971 / 3531)) (n := 12)
    (lo := (564514483 / 1000000000)) (hi := (141128621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2251 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2251 / 1280) = 1/(1280 / 2251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (564514483 / 1000000000) (141128621 / 250000000) (Real.log (2251 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2251 / 1280) = -Real.log (1280 / 2251) := by
    rw [show ((2251 / 1280) : ℝ) = ((1280 / 2251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (710637039 / 500000000) ≤ -Real.log (309 / 1280) ∧
    -Real.log (309 / 1280) ≤ (1421274081 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 309) = 1/(309 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1421274081 / 1000000000) (-710637039 / 500000000) (Real.log (309 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (281590427 / 500000000) ≤ -Real.log (160 / 281) ∧
    -Real.log (160 / 281) ≤ (112636171 / 200000000) := by
  have h := checkLog_sound (w := (121 / 441)) (n := 12)
    (lo := (281590427 / 500000000)) (hi := (112636171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 160) = 1/(160 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (281590427 / 500000000) (112636171 / 200000000) (Real.log (281 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (281 / 160) = -Real.log (160 / 281) := by
    rw [show ((281 / 160) : ℝ) = ((160 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1411612167 / 1000000000) ≤ -Real.log (39 / 160) ∧
    -Real.log (39 / 160) ≤ (141161217 / 100000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 39) = 1/(39 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-141161217 / 100000000) (-1411612167 / 1000000000) (Real.log (39 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (54946677 / 125000000) ≤ -Real.log (200000 / 310409) ∧
    -Real.log (200000 / 310409) ≤ (439573417 / 1000000000) := by
  have h := checkLog_sound (w := (110409 / 510409)) (n := 12)
    (lo := (54946677 / 125000000)) (hi := (439573417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310409 / 200000) = 1/(200000 / 310409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (54946677 / 125000000) (439573417 / 1000000000) (Real.log (310409 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (310409 / 200000) = -Real.log (200000 / 310409) := by
    rw [show ((310409 / 200000) : ℝ) = ((200000 / 310409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (803062497 / 1000000000) ≤ -Real.log (89591 / 200000) ∧
    -Real.log (89591 / 200000) ≤ (803062499 / 1000000000) := by
  have h := checkLog_sound (w := (10409 / 189591)) (n := 12)
    (lo := (109915317 / 1000000000)) (hi := (54957659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89591) = 1/(89591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-803062499 / 1000000000) (-803062497 / 1000000000) (Real.log (89591 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (88154867 / 200000000) ≤ -Real.log (100000 / 155391) ∧
    -Real.log (100000 / 155391) ≤ (6887099 / 15625000) := by
  have h := checkLog_sound (w := (55391 / 255391)) (n := 12)
    (lo := (88154867 / 200000000)) (hi := (6887099 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155391 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155391 / 100000) = 1/(100000 / 155391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (88154867 / 200000000) (6887099 / 15625000) (Real.log (155391 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (155391 / 100000) = -Real.log (100000 / 155391) := by
    rw [show ((155391 / 100000) : ℝ) = ((100000 / 155391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (807234553 / 1000000000) ≤ -Real.log (44609 / 100000) ∧
    -Real.log (44609 / 100000) ≤ (161446911 / 200000000) := by
  have h := checkLog_sound (w := (5391 / 94609)) (n := 12)
    (lo := (114087373 / 1000000000)) (hi := (57043687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 44609) = 1/(44609 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-161446911 / 200000000) (-807234553 / 1000000000) (Real.log (44609 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (88737439 / 250000000) ≤ -Real.log (1000000 / 1426109) ∧
    -Real.log (1000000 / 1426109) ≤ (354949757 / 1000000000) := by
  have h := checkLog_sound (w := (426109 / 2426109)) (n := 12)
    (lo := (88737439 / 250000000)) (hi := (354949757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1426109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1426109 / 1000000) = 1/(1000000 / 1426109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (88737439 / 250000000) (354949757 / 1000000000) (Real.log (1426109 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1426109 / 1000000) = -Real.log (1000000 / 1426109) := by
    rw [show ((1426109 / 1000000) : ℝ) = ((1000000 / 1426109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138828949 / 250000000) ≤ -Real.log (573891 / 1000000) ∧
    -Real.log (573891 / 1000000) ≤ (555315797 / 1000000000) := by
  have h := checkLog_sound (w := (426109 / 1573891)) (n := 12)
    (lo := (138828949 / 250000000)) (hi := (555315797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 573891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 573891) = 1/(573891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-555315797 / 1000000000) (-138828949 / 250000000) (Real.log (573891 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (178071251 / 500000000) ≤ -Real.log (1000000 / 1427811) ∧
    -Real.log (1000000 / 1427811) ≤ (356142503 / 1000000000) := by
  have h := checkLog_sound (w := (427811 / 2427811)) (n := 12)
    (lo := (178071251 / 500000000)) (hi := (356142503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427811 / 1000000) = 1/(1000000 / 1427811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (178071251 / 500000000) (356142503 / 1000000000) (Real.log (1427811 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1427811 / 1000000) = -Real.log (1000000 / 1427811) := by
    rw [show ((1427811 / 1000000) : ℝ) = ((1000000 / 1427811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279142961 / 500000000) ≤ -Real.log (572189 / 1000000) ∧
    -Real.log (572189 / 1000000) ≤ (558285923 / 1000000000) := by
  have h := checkLog_sound (w := (427811 / 1572189)) (n := 12)
    (lo := (279142961 / 500000000)) (hi := (558285923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 572189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 572189) = 1/(572189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-558285923 / 1000000000) (-279142961 / 500000000) (Real.log (572189 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1242635913 / 1000000000) ≤ -Real.log (125000000000 / 433091772611) ∧
    -Real.log (125000000000 / 433091772611) ≤ (248527183 / 200000000) := by
  have h := checkLog_sound (w := (183091772611 / 683091772611)) (n := 12)
    (lo := (549488733 / 1000000000)) (hi := (274744367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433091772611 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(433091772611 / 250000000000) = 1/(125000000000 / 433091772611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1242635913 / 1000000000) (248527183 / 200000000) (Real.log (433091772611 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (433091772611 / 125000000000) = -Real.log (125000000000 / 433091772611) := by
    rw [show ((433091772611 / 125000000000) : ℝ) = ((125000000000 / 433091772611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (156001111 / 125000000) ≤ -Real.log (6250000000 / 21771251317) ∧
    -Real.log (6250000000 / 21771251317) ≤ (124800889 / 100000000) := by
  have h := checkLog_sound (w := (9271251317 / 34271251317)) (n := 12)
    (lo := (138715427 / 250000000)) (hi := (554861709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21771251317 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21771251317 / 12500000000) = 1/(6250000000 / 21771251317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (156001111 / 125000000) (124800889 / 100000000) (Real.log (21771251317 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21771251317 / 6250000000) = -Real.log (6250000000 / 21771251317) := by
    rw [show ((21771251317 / 6250000000) : ℝ) = ((6250000000 / 21771251317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56891597 / 62500000) ≤ -Real.log (20000000000 / 49699646797) ∧
    -Real.log (20000000000 / 49699646797) ≤ (455132777 / 500000000) := by
  have h := checkLog_sound (w := (9699646797 / 89699646797)) (n := 12)
    (lo := (54279593 / 250000000)) (hi := (217118373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49699646797 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(49699646797 / 40000000000) = 1/(20000000000 / 49699646797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (56891597 / 62500000) (455132777 / 500000000) (Real.log (49699646797 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49699646797 / 20000000000) = -Real.log (20000000000 / 49699646797) := by
    rw [show ((49699646797 / 20000000000) : ℝ) = ((20000000000 / 49699646797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114303553 / 125000000) ≤ -Real.log (500000000000 / 1247674282449) ∧
    -Real.log (500000000000 / 1247674282449) ≤ (457214213 / 500000000) := by
  have h := checkLog_sound (w := (247674282449 / 2247674282449)) (n := 12)
    (lo := (55320311 / 250000000)) (hi := (44256249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247674282449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1247674282449 / 1000000000000) = 1/(500000000000 / 1247674282449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114303553 / 125000000) (457214213 / 500000000) (Real.log (1247674282449 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1247674282449 / 500000000000) = -Real.log (500000000000 / 1247674282449) := by
    rw [show ((1247674282449 / 500000000000) : ℝ) = ((500000000000 / 1247674282449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0114

end


